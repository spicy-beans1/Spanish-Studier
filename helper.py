"""
Español Helper - a companion app for learning Spanish while playing games.

How it works:
  1. "Select text area" -> drag a box over the game's dialogue box.
  2. Press F8 (works even while the emulator is focused) to capture the text,
     or tick "Auto-capture" and new dialogue is picked up by itself.
  3. Click any word for its translation and grammar, or use the buttons to
     translate / explain the whole sentence. The speaker buttons read the
     word or the sentence aloud in a Windows Spanish voice.
  4. "Save word" adds it to your deck; "Review" brings saved words back on a
     spaced-repetition schedule, each shown with the sentence you met it in.
  5. Words you already know can be marked as such, so only genuinely new
     words stay highlighted in the sentence.
  6. Clicking a verb offers its full conjugation table, with the form you
     clicked picked out.

Free features: OCR (Tesseract), translation (Google via deep-translator),
grammar analysis (spaCy). Optional: set ANTHROPIC_API_KEY for richer,
tutor-style explanations from Claude.
"""

import base64
import csv
import ctypes
import datetime
import hashlib
import json
import os
import queue
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import tkinter as tk
import winsound
from tkinter import messagebox, ttk

# Make Windows report real pixel coordinates so screenshots line up with
# the area you select (important on laptops with display scaling).
if sys.platform == "win32":
    try:
        ctypes.windll.shcore.SetProcessDpiAwareness(2)
    except Exception:
        try:
            ctypes.windll.user32.SetProcessDPIAware()
        except Exception:
            pass

import mss
import pytesseract
import requests
import spacy
from deep_translator import GoogleTranslator, MyMemoryTranslator
from deep_translator.exceptions import TooManyRequests
from PIL import Image, ImageChops, ImageDraw, ImageOps, ImageStat, ImageTk

APP_DIR = os.path.dirname(os.path.abspath(__file__))
CONFIG_PATH = os.path.join(APP_DIR, "config.json")
VOCAB_PATH = os.path.join(APP_DIR, "vocab.csv")
KNOWN_PATH = os.path.join(APP_DIR, "known.csv")

# Columns in vocab.csv: the first four describe the word, the rest are its
# review schedule. Older four-column files are upgraded when loaded.
VOCAB_FIELDS = ["spanish", "dictionary_form", "english", "sentence",
                "due", "interval", "ease", "reps", "lapses"]

# Words you have told the app you already know, kept by dictionary form so
# every conjugation of a verb counts once.
KNOWN_FIELDS = ["dictionary_form", "seen_as", "added", "forms"]

DEFAULT_CONFIG = {
    "region": None,              # {"left":..,"top":..,"width":..,"height":..}
    "hotkey": "f8",
    "tesseract_path": r"C:\Program Files\Tesseract-OCR\tesseract.exe",
    "scale": 3,                  # upscale factor before OCR (pixel fonts like this)
    "threshold": 140,            # 0-255, raise/lower if OCR misreads letters
    "invert": "auto",            # "auto", "yes" or "no"
    "claude_model": "claude-sonnet-5-5",
    "always_on_top": True,
    "voice": "",                 # "" = first Spanish voice; or part of a voice name
    "speech_rate": 1.0,          # 0.5 is slow and clear, 2.0 is brisk
    "auto_capture": False,       # watch the area instead of waiting for F8
    "poll_seconds": 0.6,         # how often the watcher looks at the area
    "settle_ticks": 2,           # ticks the picture must hold still before OCR
}


def load_config():
    cfg = dict(DEFAULT_CONFIG)
    try:
        with open(CONFIG_PATH, encoding="utf-8") as f:
            cfg.update(json.load(f))
    except (FileNotFoundError, json.JSONDecodeError):
        pass
    return cfg


def save_config(cfg):
    with open(CONFIG_PATH, "w", encoding="utf-8") as f:
        json.dump(cfg, f, indent=2, ensure_ascii=False)


# --------------------------------------------------------------------------
# Vocabulary deck + spaced repetition
# --------------------------------------------------------------------------

# How well you remembered a card, in button order.
GRADES = ("again", "hard", "good", "easy")
GRADE_LABELS = {"again": "Again", "hard": "Hard", "good": "Good", "easy": "Easy"}
MAX_INTERVAL = 365 * 2


def today():
    return datetime.date.today()


def new_card(spanish, dictionary_form, english, sentence):
    """A freshly saved word: due now, so it turns up in today's review."""
    return {
        "spanish": spanish,
        "dictionary_form": dictionary_form,
        "english": english,
        "sentence": sentence,
        "due": today().isoformat(),
        "interval": "0",
        "ease": "2.5",
        "reps": "0",
        "lapses": "0",
    }


def load_vocab():
    """Read vocab.csv. Words saved before reviews existed become new cards."""
    cards = read_csv(VOCAB_PATH, VOCAB_FIELDS, ("spanish",))
    for card in cards:
        if not card["due"]:
            card.update(new_card(card["spanish"], card["dictionary_form"],
                                 card["english"], card["sentence"]))
    return cards


def write_csv(path, rows):
    """Write a csv as safely as we can, then swap it into place."""
    tmp = path + ".tmp"
    with open(tmp, "w", newline="", encoding="utf-8-sig") as f:
        csv.writer(f).writerows(rows)
    try:
        os.replace(tmp, path)
    except OSError:
        # OneDrive sometimes holds a lock on the real file - write in place.
        with open(path, "w", newline="", encoding="utf-8-sig") as f:
            csv.writer(f).writerows(rows)
        try:
            os.remove(tmp)
        except OSError:
            pass


def read_csv(path, fields, header_names):
    """Read a csv into dicts, tolerating a missing file or an older layout."""
    try:
        with open(path, encoding="utf-8-sig", newline="") as f:
            rows = list(csv.reader(f))
    except (FileNotFoundError, csv.Error, UnicodeDecodeError):
        return []
    if rows and rows[0] and rows[0][0].strip().lower() in header_names:
        rows = rows[1:]
    out = []
    for row in rows:
        if not row or not row[0].strip():
            continue
        row = (row + [""] * len(fields))[:len(fields)]
        out.append(dict(zip(fields, row)))
    return out


def save_vocab(cards):
    """Write the whole deck back out - decks stay small, so this is plenty."""
    write_csv(VOCAB_PATH, [VOCAB_FIELDS] +
              [[c.get(k, "") for k in VOCAB_FIELDS] for c in cards])


def load_known():
    """Known words, keyed by dictionary form in lower case."""
    known = {}
    for entry in read_csv(KNOWN_PATH, KNOWN_FIELDS, ("dictionary_form", "word")):
        key = entry["dictionary_form"].strip().lower()
        if key:
            known[key] = entry
    return known


def save_known(known):
    entries = sorted(known.values(), key=lambda e: e["dictionary_form"].lower())
    write_csv(KNOWN_PATH, [KNOWN_FIELDS] +
              [[e.get(k, "") for k in KNOWN_FIELDS] for e in entries])


def due_cards(cards):
    """Cards scheduled for today or earlier, longest-overdue first."""
    stamp = today().isoformat()
    return sorted((c for c in cards if (c.get("due") or stamp) <= stamp),
                  key=lambda c: c.get("due") or "")


def next_due_date(cards):
    stamp = today().isoformat()
    future = [c["due"] for c in cards if c.get("due", "") > stamp]
    return min(future) if future else None


def schedule(card, grade):
    """Set a card's next review date, in place (a simplified SM-2).

    Every confident answer multiplies the gap by the card's ease factor, so
    words you know drift out to weeks and months while shaky ones keep
    coming back. Forgetting a word resets it.
    """
    ease = float(card.get("ease") or 2.5)
    reps = int(card.get("reps") or 0)
    interval = float(card.get("interval") or 0)
    lapses = int(card.get("lapses") or 0)

    if grade == "again":
        ease, reps, interval, lapses = max(1.3, ease - 0.2), 0, 0, lapses + 1
    elif grade == "hard":
        ease = max(1.3, ease - 0.15)
        interval = 1 if reps == 0 else max(1, round(interval * 1.2))
        reps += 1
    elif grade == "easy":
        ease = min(3.0, ease + 0.15)
        interval = {0: 4, 1: 9}.get(reps) or max(1, round(interval * ease * 1.3))
        reps += 1
    else:  # good
        interval = {0: 2, 1: 5}.get(reps) or max(1, round(interval * ease))
        reps += 1

    interval = min(int(interval), MAX_INTERVAL)
    card.update(due=(today() + datetime.timedelta(days=interval)).isoformat(),
                interval=str(interval), ease="%.2f" % ease,
                reps=str(reps), lapses=str(lapses))
    return card


def preview_interval(card, grade):
    """What a grade would do to this card, without changing it."""
    return int(schedule(dict(card), grade)["interval"])


def format_days(days):
    if days <= 0:
        return "today"
    if days == 1:
        return "tomorrow"
    if days < 30:
        return "in %d days" % days
    if days < 365:
        return "in %d months" % round(days / 30)
    years = days / 365
    return "in a year" if days < 400 else "in %g years" % round(years, 1)


# --------------------------------------------------------------------------
# Grammar descriptions
# --------------------------------------------------------------------------

POS_NAMES = {
    "NOUN": "noun (sustantivo)",
    "VERB": "verb (verbo)",
    "AUX": "auxiliary/helper verb (verbo auxiliar)",
    "ADJ": "adjective (adjetivo)",
    "ADV": "adverb (adverbio)",
    "PRON": "pronoun (pronombre)",
    "DET": "article/determiner (determinante)",
    "ADP": "preposition (preposición)",
    "CCONJ": "conjunction (conjunción)",
    "SCONJ": "linking word (conjunción subordinante)",
    "PROPN": "name (nombre propio)",
    "NUM": "number (número)",
    "INTJ": "interjection (interjección)",
}

SHORT_POS = {
    "NOUN": "noun", "VERB": "verb", "AUX": "helper verb", "ADJ": "adjective",
    "ADV": "adverb", "PRON": "pronoun", "DET": "article", "ADP": "preposition",
    "CCONJ": "conjunction", "SCONJ": "linking word", "PROPN": "name",
    "NUM": "number", "INTJ": "interjection",
}

PERSONS = {
    ("1", "Sing"): "yo (I)",
    ("2", "Sing"): "tú (you)",
    ("3", "Sing"): "él / ella / usted (he / she / you-formal)",
    ("1", "Plur"): "nosotros (we)",
    ("2", "Plur"): "vosotros (you all, Spain)",
    ("3", "Plur"): "ellos / ellas / ustedes (they / you all)",
}

GENDERS = {"Masc": "masculine", "Fem": "feminine"}
NUMBERS = {"Sing": "singular", "Plur": "plural"}

TIPS = {
    "ser": "Ser = 'to be' for identity, traits, time, origin. (Soy entrenador = I am a trainer.)",
    "estar": "Estar = 'to be' for location, feelings and temporary states. (Estoy cansado = I'm tired.)",
    "haber": "Haber builds perfect tenses (he visto = I have seen). 'Hay' means 'there is / there are'.",
    "tener": "Tener que + infinitive = 'to have to'. Tener is also used for age and feelings (tengo hambre = I'm hungry).",
    "ir": "Ir a + infinitive = 'going to' do something. (Voy a capturar = I'm going to catch.)",
    "gustar": "Gustar works 'backwards': me gusta = it pleases me (I like it).",
    "poder": "Poder + infinitive = 'can / be able to'.",
    "hacer": "Hacer = to do/make. Also weather (hace frío) and 'ago' (hace dos días).",
    "por": "Por: cause, exchange, movement through, duration (gracias por..., por el bosque).",
    "para": "Para: purpose, destination, deadline, recipient (para ti, para ganar).",
}


def describe_tense(mood, tense):
    """Return (short, long) description of a finite verb's tense/mood."""
    if mood == "Imp":
        return "command", "imperative (imperativo) - a command or instruction"
    if mood == "Cnd":
        return "conditional", "conditional (condicional) - 'would ...'"
    if mood == "Sub":
        if tense == "Imp":
            return "imperfect subjunctive", "imperfect subjunctive (imperfecto de subjuntivo) - hypotheticals, 'if I were...'"
        return "subjunctive", "present subjunctive (presente de subjuntivo) - wishes, doubts, after 'que' expressing desire"
    table = {
        "Pres": ("present", "present (presente)"),
        "Past": ("preterite", "preterite (pretérito indefinido) - a completed action in the past"),
        "Imp": ("imperfect", "imperfect (pretérito imperfecto) - ongoing or habitual past, 'was ...ing / used to'"),
        "Fut": ("future", "future (futuro) - 'will ...'"),
    }
    return table.get(tense, (None, None))


def explain_token(tok):
    """Full, multi-line grammar explanation of one word."""
    lines = [f"Type: {POS_NAMES.get(tok.pos_, tok.pos_.lower())}"]
    m = tok.morph.to_dict()

    if tok.pos_ in ("VERB", "AUX"):
        form = m.get("VerbForm")
        if form == "Inf":
            lines.append("Form: infinitive (infinitivo) - the basic 'to ...' form")
        elif form == "Ger":
            lines.append("Form: gerund (gerundio) - the '-ing' form (estoy luchando = I'm fighting)")
        elif form == "Part":
            lines.append("Form: past participle (participio) - like '-ed' (he ganado = I have won)")
        else:
            _, long = describe_tense(m.get("Mood"), m.get("Tense"))
            if long:
                lines.append(f"Tense: {long}")
        who = PERSONS.get((m.get("Person"), m.get("Number")))
        if who:
            lines.append(f"Who: {who}")
    else:
        if "Gender" in m:
            lines.append(f"Gender: {GENDERS.get(m['Gender'], m['Gender'])}")
        if "Number" in m:
            lines.append(f"Number: {NUMBERS.get(m['Number'], m['Number'])}")
        if tok.pos_ == "DET" and "Definite" in m:
            lines.append("Kind: definite article ('the')" if m["Definite"] == "Def"
                         else "Kind: indefinite article ('a / an / some')")
        if tok.pos_ == "PRON":
            who = PERSONS.get((m.get("Person"), m.get("Number")))
            if who:
                lines.append(f"Refers to: {who}")
            if m.get("Case") == "Acc":
                lines.append("Role: direct object (who/what receives the action)")
            elif m.get("Case") == "Dat":
                lines.append("Role: indirect object (to/for whom)")
            if m.get("Reflex") == "Yes":
                lines.append("Reflexive: the action points back at the subject (me, te, se...)")

    tip = TIPS.get(tok.lemma_.lower())
    if tip:
        lines += ["", f"Tip: {tip}"]
    return lines


def short_summary(tok):
    """One-line summary used in the whole-sentence breakdown."""
    m = tok.morph.to_dict()
    bits = [SHORT_POS.get(tok.pos_, tok.pos_.lower())]
    if tok.lemma_.lower() != tok.text.lower():
        bits.append(f"from '{tok.lemma_}'")
    if tok.pos_ in ("VERB", "AUX"):
        form = m.get("VerbForm")
        if form in ("Inf", "Ger", "Part"):
            bits.append({"Inf": "infinitive", "Ger": "gerund", "Part": "participle"}[form])
        else:
            short, _ = describe_tense(m.get("Mood"), m.get("Tense"))
            if short:
                bits.append(short)
            who = PERSONS.get((m.get("Person"), m.get("Number")))
            if who:
                bits.append(who.split(" (")[0])
    else:
        if "Gender" in m:
            bits.append(GENDERS.get(m["Gender"], m["Gender"]))
        if "Number" in m:
            bits.append(NUMBERS.get(m["Number"], m["Number"]))
    return ", ".join(bits)


# --------------------------------------------------------------------------
# Language back-end
# --------------------------------------------------------------------------

class Analyzer:
    def __init__(self):
        self.nlp = spacy.load("es_core_news_sm")
        self.cache = {}

    def parse(self, text):
        # Lowercase sentence-initial letters so the model doesn't mistake
        # e.g. "Fuiste" for a name. Same length, so offsets still match.
        normalized = re.sub(r"(^|[.!?¡¿]\s*)([A-ZÁÉÍÓÚÑ])",
                            lambda m: m.group(1) + m.group(2).lower(), text)
        return self.nlp(normalized)

    def translate(self, text):
        key = text.strip().lower()
        if not key:
            return ""
        if key not in self.cache:
            self.cache[key] = self._translate_uncached(text)
        return self.cache[key]

    def _translate_uncached(self, text):
        # Google first; if it rate-limits us, back off and retry, then fall
        # back to MyMemory so the app keeps working.
        last_err = None
        for attempt in range(3):
            try:
                return GoogleTranslator(source="es", target="en").translate(text)
            except TooManyRequests as e:
                last_err = e
                if attempt < 2:
                    time.sleep(1 + attempt)  # 1s, then 2s, then give up on Google
            except Exception as e:  # noqa: BLE001  (network error etc.: go straight to fallback)
                last_err = e
                break
        try:
            return MyMemoryTranslator(source="es-ES", target="en-US").translate(text)
        except Exception:  # noqa: BLE001
            raise last_err


def has_claude():
    return bool(os.environ.get("ANTHROPIC_API_KEY"))


def ask_claude(prompt, model):
    resp = requests.post(
        "https://api.anthropic.com/v1/messages",
        headers={
            "x-api-key": os.environ["ANTHROPIC_API_KEY"],
            "anthropic-version": "2023-06-01",
            "content-type": "application/json",
        },
        json={"model": model, "max_tokens": 800,
              "messages": [{"role": "user", "content": prompt}]},
        timeout=60,
    )
    resp.raise_for_status()
    data = resp.json()
    return "".join(b.get("text", "") for b in data.get("content", []) if b.get("type") == "text")


# --------------------------------------------------------------------------
# Screen capture + OCR
# --------------------------------------------------------------------------

def preprocess(img, cfg):
    gray = ImageOps.grayscale(img)
    s = max(1, int(cfg["scale"]))
    gray = gray.resize((gray.width * s, gray.height * s), Image.NEAREST)
    invert = cfg["invert"]
    if invert == "yes" or (invert == "auto" and ImageStat.Stat(gray).mean[0] < 128):
        gray = ImageOps.invert(gray)  # Tesseract wants dark text on light background
    thr = int(cfg["threshold"])
    bw = gray.point(lambda p: 255 if p > thr else 0)
    return ImageOps.expand(bw, border=20, fill=255)


def clean_text(text):
    text = text.replace("\n", " ")
    text = re.sub(r"[^\w¿¡!?.,;:'\"\-… ]", " ", text).replace("_", " ")
    return re.sub(r"\s+", " ", text).strip()


# Fraction of pixels that must differ before two frames count as a real
# change rather than a blinking cursor or a flicker in the background art.
FRAME_NOISE = 0.004


def grab_region(region, sct):
    shot = sct.grab(region)
    return Image.frombytes("RGB", shot.size, shot.rgb)


def frame_changed(frame, other, tolerance=FRAME_NOISE):
    """Did the picture really change? Compares two preprocessed frames."""
    if other is None or frame.size != other.size:
        return True
    diff = ImageChops.difference(frame, other)
    moved = sum(diff.histogram()[32:])  # preprocessed frames are black or white
    return moved > tolerance * frame.width * frame.height


def read_text(processed):
    """Run Tesseract over an already-preprocessed frame."""
    raw = pytesseract.image_to_string(processed, lang="spa", config="--psm 6")
    return clean_text(raw)


def ocr_region(region, cfg):
    with mss.mss() as sct:
        img = grab_region(region, sct)
    return read_text(preprocess(img, cfg)), img


class AutoCapture:
    """Watches the chosen area and reads it whenever the text settles.

    Runs on its own thread. Every tick it grabs the area and preprocesses it,
    which is cheap; OCR only happens once the picture has stopped changing.
    Waiting for it to settle is also what stops the watcher reading a line of
    dialogue while it is still typing itself out.
    """

    def __init__(self, app):
        self.app = app
        self.thread = None
        self.stop_event = threading.Event()
        self.paused = False   # held while the region selector covers the screen

    @property
    def running(self):
        return self.thread is not None and self.thread.is_alive()

    def start(self):
        if self.running:
            return
        # A fresh event per thread, so a quick stop/start can't leave the old
        # watcher running against a cleared flag.
        self.stop_event = threading.Event()
        self.thread = threading.Thread(target=self.watch, args=(self.stop_event,),
                                       daemon=True)
        self.thread.start()

    def stop(self):
        self.stop_event.set()
        self.thread = None

    def fail(self, err):
        self.app.ui_queue.put(lambda: self.app.auto_failed(err))

    def watch(self, stop):
        cfg = self.app.cfg
        previous = None   # last tick's picture, to spot movement
        read = None       # the picture we last ran OCR on
        still = 0
        try:
            sct = mss.mss()
        except Exception as e:  # noqa: BLE001
            self.fail(e)
            return
        with sct:
            while not stop.wait(max(0.1, float(cfg.get("poll_seconds") or 0.6))):
                region = cfg.get("region")
                if self.paused or not region:
                    previous, still = None, 0
                    continue
                try:
                    shot = grab_region(region, sct)
                    frame = preprocess(shot, cfg)
                except Exception:  # noqa: BLE001
                    continue  # a dropped grab shouldn't kill the watcher
                if frame_changed(frame, previous):
                    previous, still = frame, 0
                    continue
                still += 1
                if still != max(1, int(cfg.get("settle_ticks") or 2)):
                    continue  # not settled yet, or already read since it settled
                if not frame_changed(frame, read):
                    continue  # same text we read last time
                read = frame
                try:
                    text = read_text(frame)
                except Exception as e:  # noqa: BLE001
                    self.fail(e)
                    return
                if text:
                    self.app.ui_queue.put(
                        lambda t=text, i=shot: self.app.on_auto_text(t, i))


# --------------------------------------------------------------------------
# Reading text aloud
# --------------------------------------------------------------------------

# Speech goes through PowerShell's WinRT bridge rather than the classic SAPI
# interface, because the voices Windows Settings installs these days register
# themselves where only WinRT looks. Each call renders a .wav, which winsound
# then plays - that keeps starting and stopping the audio on our side.

_PS_PRELUDE = r"""
$ErrorActionPreference = 'Stop'
Add-Type -AssemblyName System.Runtime.WindowsRuntime | Out-Null
[Windows.Media.SpeechSynthesis.SpeechSynthesizer, Windows.Media, ContentType=WindowsRuntime] | Out-Null
[Windows.Storage.Streams.DataReader, Windows.Storage.Streams, ContentType=WindowsRuntime] | Out-Null
$asTask = ([System.WindowsRuntimeSystemExtensions].GetMethods() | Where-Object {
    $_.Name -eq 'AsTask' -and $_.GetParameters().Count -eq 1 -and
    $_.GetParameters()[0].ParameterType.Name -eq 'IAsyncOperation`1' })[0]
function Await($op, $type) {
    $t = $asTask.MakeGenericMethod($type).Invoke($null, @($op))
    [void]$t.Wait(20000)
    $t.Result
}
"""

_PS_LIST = _PS_PRELUDE + r"""
[Windows.Media.SpeechSynthesis.SpeechSynthesizer]::AllVoices | ForEach-Object {
    $_.DisplayName + "`t" + $_.Language + "`t" + $_.Id
}
"""

_PS_SPEAK = _PS_PRELUDE + r"""
$synth = New-Object Windows.Media.SpeechSynthesis.SpeechSynthesizer
$want = '%(voice)s'
if ($want) {
    $v = [Windows.Media.SpeechSynthesis.SpeechSynthesizer]::AllVoices |
         Where-Object { $_.Id -eq $want } | Select-Object -First 1
    if ($v) { $synth.Voice = $v }
}
$synth.Options.SpeakingRate = %(rate)s
$text = [IO.File]::ReadAllText('%(infile)s', [Text.Encoding]::UTF8)
$stream = Await $synth.SynthesizeTextToStreamAsync($text) ([Windows.Media.SpeechSynthesis.SpeechSynthesisStream])
$reader = New-Object Windows.Storage.Streams.DataReader($stream)
[void](Await $reader.LoadAsync($stream.Size) ([uint32]))
$bytes = New-Object byte[] $stream.Size
$reader.ReadBytes($bytes)
[IO.File]::WriteAllBytes('%(outfile)s', $bytes)
"""

NO_CONSOLE = 0x08000000  # don't flash a black window on every click


class NoSpanishVoice(Exception):
    """Raised when Windows has no Spanish voice to read with."""

    def __init__(self, voices):
        super().__init__("no Spanish voice installed")
        self.voices = voices  # what *is* installed, to show in the dialog


def ps_quote(text):
    return str(text).replace("'", "''")


def run_powershell(script, timeout=60):
    """Run a PowerShell script, passed as base64 so quoting can't bite."""
    encoded = base64.b64encode(script.encode("utf-16-le")).decode("ascii")
    return subprocess.run(
        ["powershell.exe", "-NoProfile", "-NonInteractive", "-EncodedCommand", encoded],
        capture_output=True, text=True, timeout=timeout, creationflags=NO_CONSOLE)


class Speaker:
    """Renders short bits of Spanish to speech and plays them."""

    def __init__(self, cfg):
        self.cfg = cfg
        self.voices = []       # [(name, language, id)] as Windows reports them
        self.listed = False
        self.cache = {}        # (voice id, rate, text) -> finished .wav
        self.folder = None
        self.turn = 0          # a newer click beats one still being rendered

    # ---------- voices ----------
    def list_voices(self, force=False):
        if self.listed and not force:
            return self.voices
        voices = []
        try:
            res = run_powershell(_PS_LIST, timeout=30)
            for line in res.stdout.splitlines():
                parts = line.split("\t")
                if len(parts) == 3 and parts[2].strip():
                    voices.append(tuple(p.strip() for p in parts))
        except (OSError, subprocess.SubprocessError):
            voices = []  # no PowerShell? then there is no speech either
        self.voices, self.listed = voices, True
        return voices

    def choose(self):
        """The voice to read with, or None if Windows has no Spanish one."""
        voices = self.list_voices()
        wanted = (self.cfg.get("voice") or "").strip().lower()
        if wanted:  # an explicit choice in config.json wins, whatever language
            for v in voices:
                if wanted in v[0].lower() or wanted in v[1].lower() or wanted in v[2].lower():
                    return v
        spanish = [v for v in voices if v[1].lower().startswith("es")]
        if not spanish:
            if self.listed and not self.voices:
                self.list_voices(force=True)  # maybe one was just installed
                spanish = [v for v in self.voices if v[1].lower().startswith("es")]
            if not spanish:
                return None
        # Prefer Spain/Mexico if several are installed; otherwise take the first.
        for tag in ("es-es", "es-mx", "es-us"):
            for v in spanish:
                if v[1].lower() == tag:
                    return v
        return spanish[0]

    # ---------- speech ----------
    def rate(self):
        try:
            return min(3.0, max(0.5, float(self.cfg.get("speech_rate") or 1.0)))
        except (TypeError, ValueError):
            return 1.0

    def render(self, text):
        """Return a .wav of `text`, rendering it if we haven't already."""
        voice = self.choose()
        if voice is None:
            raise NoSpanishVoice(self.voices)
        rate = self.rate()
        key = (voice[2], rate, text)
        if key in self.cache and os.path.exists(self.cache[key]):
            return self.cache[key], voice
        if self.folder is None:
            self.folder = tempfile.mkdtemp(prefix="espanol_helper_speech_")
        stem = hashlib.md5(("%s|%s|%s" % key).encode("utf-8")).hexdigest()[:16]
        infile = os.path.join(self.folder, stem + ".txt")
        outfile = os.path.join(self.folder, stem + ".wav")
        with open(infile, "w", encoding="utf-8") as f:
            f.write(text)
        res = run_powershell(_PS_SPEAK % {"voice": ps_quote(voice[2]),
                                          "rate": "%.2f" % rate,
                                          "infile": ps_quote(infile),
                                          "outfile": ps_quote(outfile)})
        # PowerShell writes progress chatter to stderr, so judge it by the file.
        if res.returncode != 0 or not os.path.exists(outfile):
            raise RuntimeError((res.stderr or "speech synthesis failed").strip()[-300:])
        self.cache[key] = outfile
        return outfile, voice

    def play(self, path):
        winsound.PlaySound(path, winsound.SND_FILENAME | winsound.SND_ASYNC)

    def stop(self):
        try:
            winsound.PlaySound(None, winsound.SND_PURGE)
        except RuntimeError:
            pass

    def cleanup(self):
        self.stop()
        if self.folder:
            shutil.rmtree(self.folder, ignore_errors=True)
            self.folder = None


def speaker_icon(size=16):
    """A small speaker, drawn rather than typed: Tk 8.6 cannot show emoji."""
    scale, ink = 4, (26, 77, 143, 255)
    w = size * scale
    img = Image.new("RGBA", (w, w), (0, 0, 0, 0))
    d = ImageDraw.Draw(img)
    d.rectangle([w * 0.08, w * 0.38, w * 0.26, w * 0.62], fill=ink)
    d.polygon([(w * 0.26, w * 0.40), (w * 0.48, w * 0.16),
               (w * 0.48, w * 0.84), (w * 0.26, w * 0.60)], fill=ink)
    for radius in (0.17, 0.30):
        box = [w * 0.46, w * (0.5 - radius), w * (0.46 + 2 * radius), w * (0.5 + radius)]
        d.arc(box, start=-58, end=58, fill=ink, width=int(w * 0.055))
    return ImageTk.PhotoImage(img.resize((size, size), Image.LANCZOS))


# --------------------------------------------------------------------------
# Verb conjugation
# --------------------------------------------------------------------------

# How the tables are laid out: tabs of (English name, where verbecc keeps it).
# Conditional is its own mood in the data, but learners meet it alongside the
# other indicative tenses, so it sits there.
CONJUGATION_TABS = [
    ("Indicative", [
        ("Present", ("indicativo", "presente")),
        ("Preterite", ("indicativo", "pretérito-perfecto-simple")),
        ("Imperfect", ("indicativo", "pretérito-imperfecto")),
        ("Future", ("indicativo", "futuro")),
        ("Conditional", ("condicional", "presente")),
    ]),
    ("Perfect", [
        ("Present perfect", ("indicativo", "pretérito-perfecto-compuesto")),
        ("Pluperfect", ("indicativo", "pretérito-pluscuamperfecto")),
        ("Future perfect", ("indicativo", "futuro-perfecto")),
        ("Conditional perfect", ("condicional", "perfecto")),
    ]),
    ("Subjunctive", [
        ("Present", ("subjuntivo", "presente")),
        ("Imperfect (-ra)", ("subjuntivo", "pretérito-imperfecto-1")),
        ("Imperfect (-se)", ("subjuntivo", "pretérito-imperfecto-2")),
        ("Present perfect", ("subjuntivo", "pretérito-perfecto")),
    ]),
    ("Commands", [
        ("Affirmative", ("imperativo", "afirmativo")),
        ("Negative", ("imperativo", "negativo")),
    ]),
]

# One row per person, using the same wording as the single-word explanations.
CONJUGATION_ROWS = [
    ("1", "s", "yo"), ("2", "s", "tú"), ("3", "s", "él / ella / usted"),
    ("1", "p", "nosotros"), ("2", "p", "vosotros"), ("3", "p", "ellos / ellas / ustedes"),
]
# Which pronoun to take when the data offers several for one row (it lists
# él, ella and usted separately, and vos alongside tú).
CANONICAL_PRONOUNS = ("yo", "tú", "él", "nosotros", "vosotros", "ellos")

SIMPLE_FORMS = [("Infinitive", "infinitivo"), ("Gerund", "gerundio"),
                ("Participle", "participo")]


class Conjugator:
    """Lazy wrapper around verbecc, which is slow and heavy to import."""

    def __init__(self):
        self.engine = None
        self.cache = {}

    def load(self):
        if self.engine is not None:
            return self.engine
        import logging
        logging.getLogger("verbecc").setLevel(logging.WARNING)
        from verbecc import CompleteConjugator
        # verbecc sets its own level while importing, so quieten it again or
        # it chatters into the console window on every launch.
        quiet = logging.getLogger("verbecc")
        quiet.setLevel(logging.WARNING)
        quiet.propagate = False
        self.engine = CompleteConjugator(lang="es")
        return self.engine

    def conjugate(self, infinitive):
        """{'verb': {...}, 'moods': {mood: {tense: [entries]}}} for one verb."""
        key = infinitive.strip().lower()
        if key not in self.cache:
            self.load()
            self.cache[key] = json.loads(self.engine.conjugate(key).to_json())
        return self.cache[key]


# spaCy's small model invents infinitives for strong preterites - "tuviste"
# comes back as "tuviste", "perdiste" as "perdistir". Suffix surgery rescues
# the regular verbs; these stems rescue the irregular ones.
STRONG_PRETERITE_STEMS = {
    "estuv": "estar", "anduv": "andar", "conduj": "conducir",
    "produj": "producir", "traduj": "traducir", "tuv": "tener", "hub": "haber",
    "pud": "poder", "pus": "poner", "quis": "querer", "sup": "saber",
    "vin": "venir", "hic": "hacer", "hiz": "hacer", "dij": "decir",
    "traj": "traer", "cup": "caber", "fu": "ir", "di": "dar", "vi": "ver",
}


def simple_forms(data):
    """Every one-word form in a conjugation table, lower case.

    Compound tenses ("he hablado") are left out on purpose: they would drag
    in forms of haber, and the participle is already listed on its own.
    """
    forms = set()
    for mood in data.get("moods", {}).values():
        for entries in mood.values():
            for entry in entries:
                text = (entry.get("c") or [""])[0].strip()
                pronoun = (entry.get("pr") or "").strip()
                if pronoun and text.lower().startswith(pronoun.lower() + " "):
                    text = text[len(pronoun) + 1:]
                words = [w for w in text.lower().split() if w != "no"]
                if len(words) == 1:
                    forms.add(words[0])
    return forms


def infinitive_candidates(word, lemma=""):
    """Infinitives worth testing for a conjugated form, best guess first."""
    out = []
    if lemma:
        out.append(lemma.strip().lower())
    for stem in sorted(STRONG_PRETERITE_STEMS, key=len, reverse=True):
        if word.startswith(stem):
            out.append(STRONG_PRETERITE_STEMS[stem])
    out.append(word)
    for cut in range(1, 6):  # build the infinitive back up from the stem
        if len(word) - cut < 2:
            break
        for ending in ("ar", "er", "ir"):
            out.append(word[:-cut] + ending)
    return out


def resolve_infinitive(conjugator, surface, lemma=""):
    """Find the infinitive whose table really contains `surface`.

    Every candidate is checked against the conjugation it produces, so a bad
    guess can never put a wrong table on screen.
    """
    word = (surface or "").strip().lower()
    if not word:
        return "", None
    guessed = ("", None)
    seen = set()
    for candidate in infinitive_candidates(word, lemma):
        if (not candidate or candidate in seen
                or not candidate.endswith(("ar", "er", "ir"))):
            continue
        seen.add(candidate)
        try:
            data = conjugator.conjugate(candidate)
        except Exception:  # noqa: BLE001
            continue
        if word not in simple_forms(data):
            continue
        if not data.get("verb", {}).get("predicted"):
            return candidate, data  # a verb verbecc actually knows
        # An invented infinitive can match by chance - spaCy's "perdistir"
        # conjugates to "perdiste" - so hold it and keep looking for a real one.
        # Only spaCy's own lemma is worth holding: a candidate this function
        # built by chopping letters off ("mochila" -> "mochilar") is no
        # evidence of anything.
        if guessed[1] is None and candidate == (lemma or "").strip().lower():
            guessed = (candidate, data)
    return guessed


def tense_forms(data, mood, tense):
    """{(person, number): form} for one tense, pronouns stripped off."""
    entries = data.get("moods", {}).get(mood, {}).get(tense, [])
    forms = {}
    for entry in entries:
        slot = (entry.get("p", ""), entry.get("n", ""))
        pronoun = (entry.get("pr") or "").strip()
        if slot in forms and pronoun.lower() not in CANONICAL_PRONOUNS:
            continue  # keep él rather than ella/usted, tú rather than vos
        text = (entry.get("c") or [""])[0].strip()
        if pronoun and text.lower().startswith(pronoun.lower() + " "):
            text = text[len(pronoun) + 1:]
        forms[slot] = text
    return forms


def simple_form(data, mood):
    entries = data.get("moods", {}).get(mood, {}).get(mood, [])
    if not entries:
        return ""
    return (entries[0].get("c") or [""])[0].strip()


class ConjugationWindow(tk.Toplevel):
    """The full table for one verb, with the form you clicked picked out."""

    def __init__(self, app, data, clicked, english=""):
        super().__init__(app.root)
        self.app = app
        verb = data.get("verb", {})
        self.infinitive = verb.get("infinitive", "?")
        self.clicked = (clicked or "").strip().lower()

        self.title(f"Conjugation - {self.infinitive}")
        self.geometry("860x520")
        self.attributes("-topmost", app.cfg["always_on_top"])

        head = ttk.Frame(self, padding=(12, 10, 12, 0))
        head.pack(fill="x")
        ttk.Label(head, text=self.infinitive, font=("Segoe UI", 20, "bold"),
                  foreground="#1a4d8f").pack(side="left")
        if english:
            ttk.Label(head, text=f"  {english}", font=("Segoe UI", 13),
                      foreground="#2d6a2d").pack(side="left", padx=(8, 0))
        ttk.Button(head, text="Close", command=self.destroy).pack(side="right")

        line = " · ".join(f"{name}: {simple_form(data, mood)}"
                          for name, mood in SIMPLE_FORMS if simple_form(data, mood))
        if line:
            ttk.Label(self, text=line, padding=(12, 2), foreground="#555").pack(anchor="w")
        if verb.get("predicted"):
            ttk.Label(self, padding=(12, 2), foreground="#9a6a00",
                      text="This verb isn't in the conjugation data, so these forms were "
                           "predicted from similar verbs - treat them with care.").pack(anchor="w")

        book = ttk.Notebook(self, padding=(8, 6))
        book.pack(fill="both", expand=True)
        for title, tenses in CONJUGATION_TABS:
            page = ttk.Frame(book, padding=8)
            book.add(page, text=title)
            self.build_table(page, data, tenses)

        ttk.Label(self, padding=(12, 0, 12, 8), foreground="#888",
                  text="The form you clicked is highlighted.").pack(anchor="w")
        self.bind("<Escape>", lambda e: self.destroy())
        self.focus_force()

    def build_table(self, page, data, tenses):
        columns = [(name, tense_forms(data, mood, tense)) for name, (mood, tense) in tenses]
        for col, (name, _) in enumerate(columns, start=1):
            ttk.Label(page, text=name, font=("Segoe UI", 10, "bold"),
                      foreground="#444").grid(row=0, column=col, padx=8, pady=(0, 6), sticky="w")
        for row, (person, number, label) in enumerate(CONJUGATION_ROWS, start=1):
            ttk.Label(page, text=label, foreground="#666").grid(
                row=row, column=0, sticky="e", padx=(0, 10), pady=2)
            for col, (_, forms) in enumerate(columns, start=1):
                text = forms.get((person, number), "")
                cell = tk.Label(page, text=text or "-", font=("Segoe UI", 11),
                                anchor="w", padx=5, pady=2,
                                bg=self.cget("bg"), fg="#222")
                if text and self.matches(text):
                    cell.configure(bg="#ffe08a", font=("Segoe UI", 11, "bold"), fg="#000")
                cell.grid(row=row, column=col, sticky="w", padx=4)
        for col in range(1, len(columns) + 1):
            page.grid_columnconfigure(col, weight=1)

    def matches(self, form):
        """Is this cell the word the user clicked? Compounds count too."""
        if not self.clicked:
            return False
        parts = form.lower().split()
        return self.clicked == form.lower() or self.clicked in parts


class RegionSelector(tk.Toplevel):
    """Dim the screen and let the user drag a rectangle."""

    def __init__(self, master, on_done):
        super().__init__(master)
        self.on_done = on_done
        with mss.mss() as sct:
            mon = sct.monitors[0]  # the whole desktop, all monitors
        self.overrideredirect(True)
        self.geometry(f"{mon['width']}x{mon['height']}+{mon['left']}+{mon['top']}")
        self.attributes("-alpha", 0.3)
        self.attributes("-topmost", True)
        self.canvas = tk.Canvas(self, cursor="cross", bg="black", highlightthickness=0)
        self.canvas.pack(fill="both", expand=True)
        self.canvas.create_text(
            40, 40, anchor="nw", fill="white", font=("Segoe UI", 20, "bold"),
            text="Drag over the game's dialogue box.  Esc to cancel.")
        self.start = None
        self.rect = None
        self.canvas.bind("<ButtonPress-1>", self.press)
        self.canvas.bind("<B1-Motion>", self.drag)
        self.canvas.bind("<ButtonRelease-1>", self.release)
        self.bind("<Escape>", lambda e: self.finish(None))
        self.focus_force()

    def press(self, e):
        self.start = (e.x, e.y, e.x_root, e.y_root)
        self.rect = self.canvas.create_rectangle(e.x, e.y, e.x, e.y, outline="red", width=3)

    def drag(self, e):
        if self.rect:
            self.canvas.coords(self.rect, self.start[0], self.start[1], e.x, e.y)

    def release(self, e):
        if not self.start:
            return
        x1, y1 = self.start[2], self.start[3]
        x2, y2 = e.x_root, e.y_root
        region = {"left": min(x1, x2), "top": min(y1, y2),
                  "width": abs(x2 - x1), "height": abs(y2 - y1)}
        self.finish(region if region["width"] > 10 and region["height"] > 10 else None)

    def finish(self, region):
        self.destroy()
        self.on_done(region)


# --------------------------------------------------------------------------
# Main window
# --------------------------------------------------------------------------

class ReviewWindow(tk.Toplevel):
    """Flashcards for saved words, each shown with the sentence it came from.

    Space reveals the answer, then 1-4 (or the buttons) say how well you knew
    it. "Again" puts the card back into this session; the others push it out
    by days, weeks or months depending on how often you have recalled it.
    """

    def __init__(self, app):
        super().__init__(app.root)
        self.app = app
        self.queue = due_cards(app.vocab)
        self.card = None
        self.revealed = False
        self.done = 0

        self.title("Review")
        self.geometry("580x560")
        self.attributes("-topmost", app.cfg["always_on_top"])
        self.protocol("WM_DELETE_WINDOW", self.close)
        self.build_ui()

        self.bind("<space>", self.on_space)
        self.bind("<Return>", self.on_space)
        self.bind("<Escape>", lambda e: self.close())
        for n, g in enumerate(GRADES, 1):
            self.bind(str(n), lambda e, g=g: self.grade(g))
        self.focus_force()
        self.next_card()

    # ---------- UI ----------
    def build_ui(self):
        self.progress = ttk.Label(self, foreground="#555", padding=(10, 8))
        self.progress.pack(fill="x")

        footer = ttk.Frame(self, padding=(10, 6))
        footer.pack(side="bottom", fill="x")
        self.remove_btn = ttk.Button(footer, text="Remove this card",
                                     command=self.remove_card)
        self.remove_btn.pack(side="left")
        ttk.Button(footer, text="Close", command=self.close).pack(side="right")
        ttk.Label(footer, foreground="#888",
                  text="space = show answer   |   1-4 = how well you knew it"
                  ).pack(side="left", padx=10)

        # Packed only while an answer is showing, just above the footer.
        self.grades = ttk.Frame(self)
        self.grade_btns = {}
        for g in GRADES:
            btn = ttk.Button(self.grades, command=lambda g=g: self.grade(g))
            btn.pack(side="left", padx=3, expand=True, fill="x")
            self.grade_btns[g] = btn

        card = ttk.Frame(self, padding=10)
        card.pack(fill="both", expand=True)
        self.word = ttk.Label(card, font=("Segoe UI", 26, "bold"),
                              foreground="#1a4d8f", wraplength=520, justify="center")
        self.prompt = ttk.Label(card, foreground="#888", wraplength=520,
                                justify="center")
        self.answer = ttk.Label(card, font=("Segoe UI", 18), foreground="#2d6a2d",
                                wraplength=520, justify="center")
        self.lemma = ttk.Label(card, foreground="#666", wraplength=520,
                               justify="center")
        self.hint_btn = ttk.Button(card, text="Show the sentence",
                                   command=self.show_context)
        self.reveal_btn = ttk.Button(card, text="Show answer (space)",
                                     command=self.reveal)
        self.context_title = ttk.Label(card, foreground="#888",
                                       text="Where you saw it:")
        self.context = tk.Text(card, height=4, wrap="word", relief="flat",
                               font=("Segoe UI", 13), bg="#fffdf5", padx=8, pady=6)
        self.context.tag_configure("hl", font=("Segoe UI", 13, "bold"),
                                   background="#ffe08a")
        self.context.configure(state="disabled")
        self.context.bind("<Configure>", self.fit_context)
        self.card_widgets = (self.word, self.prompt, self.answer, self.lemma,
                             self.hint_btn, self.reveal_btn, self.context_title,
                             self.context)

    def show_context(self):
        """Show the captured sentence, with the word itself highlighted."""
        sentence = (self.card.get("sentence") or "").strip() if self.card else ""
        word = self.card.get("spanish", "") if self.card else ""
        self.context.configure(state="normal")
        self.context.delete("1.0", "end")
        at = sentence.lower().find(word.lower()) if word else -1
        if not sentence:
            self.context.insert("end", "(no sentence was saved with this word)")
        elif at < 0:
            self.context.insert("end", sentence)
        else:
            self.context.insert("end", sentence[:at])
            self.context.insert("end", sentence[at:at + len(word)], "hl")
            self.context.insert("end", sentence[at + len(word):])
        self.context.configure(state="disabled")
        self.hint_btn.pack_forget()
        self.context_title.pack(anchor="w", pady=(12, 2))
        self.context.pack(fill="x")
        self.fit_context()

    def fit_context(self, _event=None):
        """Grow the box to the sentence: a captured line can run long.

        How many lines the text needs depends on how wide the box ended up,
        so this waits for Tk to lay the box out and re-runs on every resize.
        """
        if not self.winfo_exists():
            return
        self.context.update_idletasks()
        if self.context.winfo_width() <= 1:
            self.after(30, self.fit_context)  # not laid out yet, try again
            return
        try:
            needed = self.context.count("1.0", "end", "displaylines")[0]
        except (tk.TclError, TypeError, IndexError):
            return
        self.context.configure(height=max(2, min(int(needed), 9)))
        found = self.context.tag_ranges("hl")
        if found:
            self.context.see(found[0])  # keep the word itself in view

    # ---------- card flow ----------
    def next_card(self):
        self.revealed = False
        for w in self.card_widgets:
            w.pack_forget()
        self.grades.pack_forget()
        if not self.queue:
            self.finish()
            return
        self.card = self.queue.pop(0)
        self.remove_btn.state(["!disabled"])
        self.word.configure(text=self.card["spanish"] or "(blank)",
                            foreground="#1a4d8f")
        self.word.pack(pady=(20, 4))
        self.prompt.configure(text="What does it mean?")
        self.prompt.pack()
        self.hint_btn.pack(pady=10)
        self.reveal_btn.pack(pady=4)
        left = len(self.queue) + 1
        self.progress.configure(
            text="%d card%s to go   |   %d reviewed this session"
                 % (left, "" if left == 1 else "s", self.done))

    def reveal(self):
        if self.revealed or not self.card:
            return
        self.revealed = True
        card = self.card
        self.prompt.pack_forget()
        self.reveal_btn.pack_forget()
        self.answer.configure(text=card.get("english") or "(no translation saved)")
        self.answer.pack(pady=(8, 2))
        lemma = card.get("dictionary_form") or ""
        if lemma and lemma.lower() != (card.get("spanish") or "").lower():
            self.lemma.configure(text="dictionary form: " + lemma)
            self.lemma.pack()
        self.show_context()
        for n, g in enumerate(GRADES, 1):
            when = ("this session" if g == "again"
                    else format_days(preview_interval(card, g)))
            self.grade_btns[g].configure(
                text="%d. %s\n%s" % (n, GRADE_LABELS[g], when))
        self.grades.pack(side="bottom", fill="x", padx=8, pady=(0, 4))

    def on_space(self, _event=None):
        if self.card and not self.revealed:
            self.reveal()
        elif self.card:
            self.grade("good")

    def grade(self, grade):
        if not self.revealed or not self.card:
            return
        card = self.card
        schedule(card, grade)
        self.done += 1
        if grade == "again":
            self.queue.append(card)  # come back to it before the session ends
        self.card = None
        self.persist()
        self.next_card()

    def remove_card(self):
        if not self.card:
            return
        word = self.card.get("spanish") or "this card"
        if not messagebox.askyesno("Remove card",
                                   "Remove %r from your vocabulary?" % word,
                                   parent=self):
            return
        dropped = self.card
        self.app.vocab[:] = [c for c in self.app.vocab if c is not dropped]
        self.queue = [c for c in self.queue if c is not dropped]
        self.card = None
        self.persist()
        self.next_card()

    def persist(self):
        try:
            save_vocab(self.app.vocab)
        except OSError as e:  # noqa: BLE001
            messagebox.showwarning("Could not save",
                                   "vocab.csv could not be written:\n%s" % e,
                                   parent=self)
        self.app.refresh_due()

    def finish(self):
        self.card = None
        for w in self.card_widgets:
            w.pack_forget()
        self.grades.pack_forget()
        self.remove_btn.state(["disabled"])
        total = len(self.app.vocab)
        if not total:
            headline = "No saved words yet"
            sub_line = "Click a word, then 'Save word', to start your deck."
        else:
            headline = "All caught up!"
            nxt = next_due_date(self.app.vocab)
            if nxt:
                days = (datetime.date.fromisoformat(nxt) - today()).days
                sub_line = "Next review %s (%s)." % (format_days(days), nxt)
            else:
                sub_line = "Nothing else is scheduled."
        self.word.configure(text=headline, foreground="#2d6a2d")
        self.word.pack(pady=(40, 6))
        self.prompt.configure(text=sub_line)
        self.prompt.pack()
        self.progress.configure(text="%d reviewed this session   |   %d word%s saved"
                                     % (self.done, total, "" if total == 1 else "s"))

    def close(self):
        self.app.review_win = None
        self.app.refresh_due()
        self.destroy()


class App:
    def __init__(self, root):
        self.root = root
        self.cfg = load_config()
        self.analyzer = None
        self.doc = None
        self.text = ""
        self.selected_index = None
        self.last_word = None  # (word, lemma, english, sentence)
        self.ui_queue = queue.Queue()
        self.vocab = load_vocab()
        self.known = load_known()
        self.known_forms = set()
        self.rebuild_known_forms()
        self.conjugator = Conjugator()
        self.review_win = None
        self.auto = AutoCapture(self)
        self.speaker = Speaker(self.cfg)

        root.title("Español Helper")
        root.geometry("680x780")
        root.attributes("-topmost", self.cfg["always_on_top"])
        root.protocol("WM_DELETE_WINDOW", self.on_close)

        self.build_ui()
        self.setup_tesseract()
        self.setup_hotkey()
        root.after(100, self.process_queue)

        self.set_status("Loading Spanish language model...")
        self.run_bg(Analyzer, self.on_analyzer_ready)

    # ---------- threading helpers ----------
    def run_bg(self, work, done):
        def target():
            try:
                res, err = work(), None
            except Exception as e:  # noqa: BLE001
                res, err = None, e
            self.ui_queue.put(lambda: done(res, err))
        threading.Thread(target=target, daemon=True).start()

    def process_queue(self):
        while not self.ui_queue.empty():
            self.ui_queue.get_nowait()()
        self.root.after(100, self.process_queue)

    # ---------- UI ----------
    def build_ui(self):
        style = ttk.Style()
        try:
            style.theme_use("vista")
        except tk.TclError:
            pass

        top = ttk.Frame(self.root, padding=6)
        top.pack(fill="x")
        ttk.Button(top, text="Select text area", command=self.select_region).pack(side="left")
        ttk.Button(top, text=f"Capture ({self.cfg['hotkey'].upper()})",
                   command=self.capture).pack(side="left", padx=4)
        self.auto_var = tk.BooleanVar(value=self.cfg.get("auto_capture", False))
        ttk.Checkbutton(top, text="Auto-capture", variable=self.auto_var,
                        command=self.toggle_auto).pack(side="left", padx=(0, 8))
        ttk.Button(top, text="Vocab list", command=self.show_vocab).pack(side="left")
        self.review_btn = ttk.Button(top, text="Review", command=self.open_review)
        self.review_btn.pack(side="left", padx=4)
        self.pin_var = tk.BooleanVar(value=self.cfg["always_on_top"])
        ttk.Checkbutton(top, text="Stay on top", variable=self.pin_var,
                        command=self.toggle_pin).pack(side="right")

        self.status = ttk.Label(self.root, foreground="#555", padding=(8, 0))
        self.status.pack(fill="x")

        self.preview = ttk.Label(self.root)
        self.preview.pack(pady=4)

        ttk.Label(self.root, padding=(8, 4, 8, 0),
                  text="Recognized text (fix OCR mistakes, or paste any Spanish):").pack(anchor="w")
        edit = ttk.Frame(self.root, padding=(8, 2))
        edit.pack(fill="x")
        self.raw_text = tk.Text(edit, height=3, wrap="word", font=("Segoe UI", 11))
        self.raw_text.pack(side="left", fill="x", expand=True)
        ttk.Button(edit, text="Analyze", command=self.analyze_from_box).pack(side="left", padx=(6, 0))

        head = ttk.Frame(self.root, padding=(8, 6, 8, 0))
        head.pack(fill="x")
        ttk.Label(head, text="Click any word:").pack(side="left")
        self.speaker_img = speaker_icon()  # keep a reference or Tk drops it
        self.say_sentence_btn = ttk.Button(head, image=self.speaker_img, text=" Hear sentence",
                                           compound="left", command=self.say_sentence)
        self.say_sentence_btn.pack(side="right")
        self.say_word_btn = ttk.Button(head, image=self.speaker_img, text=" Hear word",
                                       compound="left", command=self.say_word,
                                       state="disabled")
        self.say_word_btn.pack(side="right", padx=6)
        self.sentence = tk.Text(self.root, height=4, wrap="word", font=("Segoe UI", 16),
                                cursor="arrow", padx=8, pady=6, relief="flat", bg="#fffdf5")
        self.sentence.pack(fill="x", padx=8)
        # New words stand out; words you are already dealing with recede.
        self.sentence.tag_configure("new", foreground="#1a4d8f")
        self.sentence.tag_configure("deck", foreground="#6b6b6b", underline=True)
        self.sentence.tag_configure("known", foreground="#8a8a8a")
        self.sentence.tag_configure("selected", background="#ffe08a")
        self.sentence.configure(state="disabled")

        self.auto_trans = ttk.Label(self.root, wraplength=600, justify="left",
                                    foreground="#2d6a2d", font=("Segoe UI", 12, "italic"),
                                    padding=(8, 4, 8, 0))
        self.auto_trans.pack(fill="x")

        actions = ttk.Frame(self.root, padding=(8, 6))
        actions.pack(fill="x")
        ttk.Button(actions, text="Translate sentence", command=self.translate_sentence).pack(side="left")
        ttk.Button(actions, text="Explain grammar", command=self.explain_sentence).pack(side="left", padx=4)
        self.save_btn = ttk.Button(actions, text="Save word", command=self.save_word, state="disabled")
        self.save_btn.pack(side="left")
        self.known_btn = ttk.Button(actions, text="Mark known",
                                    command=self.toggle_known, state="disabled")
        self.known_btn.pack(side="left", padx=4)
        self.conj_btn = ttk.Button(actions, text="Conjugation",
                                   command=self.show_conjugation, state="disabled")
        self.conj_btn.pack(side="left", padx=(0, 4))
        self.ask_btn = ttk.Button(actions, text="Ask Claude about word",
                                  command=self.ask_about_word, state="disabled")
        self.ask_btn.pack(side="left")

        info_frame = ttk.Frame(self.root, padding=(8, 0, 8, 8))
        info_frame.pack(fill="both", expand=True)
        self.info = tk.Text(info_frame, wrap="word", font=("Segoe UI", 11),
                            padx=8, pady=6, relief="flat", bg="#f6f7f9")
        scroll = ttk.Scrollbar(info_frame, command=self.info.yview)
        self.info.configure(yscrollcommand=scroll.set)
        scroll.pack(side="right", fill="y")
        self.info.pack(side="left", fill="both", expand=True)
        self.info.tag_configure("h", font=("Segoe UI", 14, "bold"))
        self.info.tag_configure("b", font=("Segoe UI", 11, "bold"))
        self.info.tag_configure("sub", foreground="#666")
        self.set_info([("Welcome! Click 'Select text area', drag over your game's dialogue box, "
                        "then press F8 when new text appears - or tick 'Auto-capture' "
                        "and it will read each new line for you.", "sub")])
        self.refresh_due()

    def set_status(self, text):
        self.status.configure(text=text)

    def set_info(self, parts):
        self.info.configure(state="normal")
        self.info.delete("1.0", "end")
        for text, tag in parts:
            self.info.insert("end", text, tag)
        self.info.configure(state="disabled")

    def toggle_pin(self):
        self.cfg["always_on_top"] = self.pin_var.get()
        self.root.attributes("-topmost", self.cfg["always_on_top"])
        save_config(self.cfg)

    # ---------- setup ----------
    def setup_tesseract(self):
        path = self.cfg.get("tesseract_path")
        if path and os.path.exists(path):
            pytesseract.pytesseract.tesseract_cmd = path

    def setup_hotkey(self):
        try:
            import keyboard
            keyboard.add_hotkey(self.cfg["hotkey"], lambda: self.ui_queue.put(self.capture))
        except Exception:
            # Fall back to a hotkey that only works while this window is focused
            try:
                self.root.bind(f"<{self.cfg['hotkey'].upper()}>", lambda e: self.capture())
            except tk.TclError:
                pass

    def on_analyzer_ready(self, analyzer, err):
        if err:
            messagebox.showerror("Missing language model",
                                 "Couldn't load the Spanish model. Run setup.bat first.\n\n" + str(err))
            self.set_status("Spanish model missing - run setup.bat")
            return
        self.analyzer = analyzer
        extra = "" if has_claude() else "  (Claude explanations off - see README)"
        self.sync_auto()  # the model is up, so the watcher can analyze now
        if self.auto.running:
            extra = "  Auto-capture is on." + extra
        self.set_status("Ready." + extra)

    # ---------- capture ----------
    def select_region(self):
        self.auto.paused = True  # the dimmed overlay is not worth reading
        self.root.withdraw()
        self.root.after(200, lambda: RegionSelector(self.root, self.on_region))

    def on_region(self, region):
        self.root.deiconify()
        self.auto.paused = False
        if not region:
            self.set_status("Selection cancelled.")
            return
        self.cfg["region"] = region
        save_config(self.cfg)
        self.sync_auto()
        self.set_status("Area saved. Capturing a test...")
        self.capture()

    # ---------- auto-capture ----------
    def sync_auto(self):
        """Run the watcher only when it is wanted and has what it needs."""
        if self.auto_var.get() and self.cfg.get("region") and self.analyzer:
            self.auto.start()
        else:
            self.auto.stop()

    def toggle_auto(self):
        on = self.auto_var.get()
        if on and not self.cfg.get("region"):
            self.auto_var.set(False)
            self.set_status("First click 'Select text area' and drag over the dialogue box.")
            return
        self.cfg["auto_capture"] = on
        save_config(self.cfg)
        self.sync_auto()
        if not on:
            self.set_status(f"Auto-capture off - press {self.cfg['hotkey'].upper()} to capture.")
        elif self.analyzer:
            self.set_status("Auto-capture on - watching that area for new text.")
        else:
            self.set_status("Auto-capture on - starting once the Spanish model finishes loading.")

    def on_auto_text(self, text, img):
        """New dialogue the watcher found (runs on the UI thread)."""
        if not self.analyzer or text == self.text:
            return
        if sum(c.isalpha() for c in text) < 2:
            return  # an empty or closing text box, not a line of dialogue
        if self.root.focus_get() is self.raw_text:
            return  # someone is fixing the text by hand - leave it alone
        self.show_preview(img)
        self.raw_text.delete("1.0", "end")
        self.raw_text.insert("1.0", text)
        self.analyze(text)
        self.set_status(f"Auto-captured at {time.strftime('%H:%M:%S')} - "
                        "watching for the next line.")

    def auto_failed(self, err):
        """OCR broke inside the watcher: switch it off and explain why."""
        self.auto_var.set(False)
        self.cfg["auto_capture"] = False
        save_config(self.cfg)  # don't start broken again on the next launch
        self.auto.stop()
        self.on_ocr_done(None, err)

    def capture(self):
        region = self.cfg.get("region")
        if not region:
            self.set_status("First click 'Select text area' and drag over the dialogue box.")
            return
        self.set_status("Reading text...")
        self.run_bg(lambda: ocr_region(region, self.cfg), self.on_ocr_done)

    def on_ocr_done(self, result, err):
        if err:
            if isinstance(err, pytesseract.TesseractNotFoundError):
                msg = "Tesseract isn't installed or its path in config.json is wrong. See README."
            elif "spa" in str(err):
                msg = "Tesseract's Spanish data is missing. Reinstall Tesseract and tick Spanish."
            else:
                msg = f"OCR failed: {err}"
            self.set_status(msg)
            return
        text, img = result
        self.show_preview(img)
        self.raw_text.delete("1.0", "end")
        self.raw_text.insert("1.0", text)
        if not text:
            self.set_status("No text found. Reselect the area, or adjust 'threshold' in config.json.")
            return
        self.analyze(text)

    def show_preview(self, img):
        thumb = img.copy()
        thumb.thumbnail((600, 120))
        self._preview_img = ImageTk.PhotoImage(thumb)  # keep a reference
        self.preview.configure(image=self._preview_img)

    # ---------- analysis ----------
    def analyze_from_box(self):
        text = re.sub(r"\s+", " ", self.raw_text.get("1.0", "end")).strip()
        if text:
            self.analyze(text)

    def analyze(self, text):
        if not self.analyzer:
            self.set_status("Still loading the Spanish model, try again in a moment.")
            return
        self.text = text
        self.doc = self.analyzer.parse(text)
        self.selected_index = None
        self.last_word = None
        self.save_btn.configure(state="disabled")
        self.ask_btn.configure(state="disabled")
        self.say_word_btn.configure(state="disabled")
        self.known_btn.configure(state="disabled", text="Mark known")
        self.conj_btn.configure(state="disabled")
        self.render_sentence()
        new = self.count_new()
        self.set_info([
            ("%d new word%s in this line.\n" % (new, "" if new == 1 else "s"), "b"),
            ("Blue = new to you.  Underlined = in your review deck.  "
             "Grey = marked known.\nClick a word to see its meaning and grammar.", "sub")])
        self.set_status("Ready.")
        self.auto_translate(text)

    def auto_translate(self, text):
        """Show the English translation of the whole phrase under the sentence."""
        doc = self.doc
        self.auto_trans.configure(text="Translating...")

        def done(res, err):
            if self.doc is not doc:
                return  # a newer capture replaced this one
            self.auto_trans.configure(
                text=res if not err else "(Translation unavailable - check your internet, "
                                         "or wait a moment if Google is rate-limiting.)")

        self.run_bg(lambda: self.analyzer.translate(text), done)

    def orig(self, tok):
        """The word exactly as it appeared (original capitalization)."""
        return self.text[tok.idx:tok.idx + len(tok.text)]

    def deck_forms(self):
        """Every spelling already in the review deck, lower case."""
        forms = set()
        for card in self.vocab:
            forms.add((card.get("spanish") or "").strip().lower())
            forms.add((card.get("dictionary_form") or "").strip().lower())
        forms.discard("")
        return forms

    def rebuild_known_forms(self):
        """Flatten known words into every spelling that should count."""
        forms = set(self.known)
        for entry in self.known.values():
            forms.update((entry.get("forms") or "").lower().split())
        forms.discard("")
        self.known_forms = forms

    def word_state(self, tok, deck=None):
        """'known', 'deck' or 'new' - which decides how the word is drawn."""
        forms = {tok.lemma_.strip().lower(), tok.text.strip().lower()}
        forms.discard("")
        if forms & self.known_forms:
            return "known"
        if forms & (self.deck_forms() if deck is None else deck):
            return "deck"
        return "new"

    def count_new(self):
        deck = self.deck_forms()
        return sum(1 for tok in self.doc
                   if tok.is_alpha and self.word_state(tok, deck) == "new")

    def render_sentence(self):
        s = self.sentence
        deck = self.deck_forms()
        s.configure(state="normal")
        s.delete("1.0", "end")
        for i, tok in enumerate(self.doc):
            tag = f"tok{i}"
            tags = (tag,) if not tok.is_alpha else (tag, self.word_state(tok, deck))
            s.insert("end", self.orig(tok), tags)
            if tok.is_alpha:
                s.tag_bind(tag, "<Button-1>", lambda e, i=i: self.show_word(i))
                s.tag_bind(tag, "<Enter>", lambda e: s.configure(cursor="hand2"))
                s.tag_bind(tag, "<Leave>", lambda e: s.configure(cursor="arrow"))
            s.insert("end", tok.whitespace_)
        s.configure(state="disabled")
        if self.selected_index is not None:
            self.mark_selected(self.selected_index)

    def mark_selected(self, i):
        self.sentence.tag_remove("selected", "1.0", "end")
        found = self.sentence.tag_ranges(f"tok{i}")
        if found:
            self.sentence.tag_add("selected", found[0], found[1])

    def show_word(self, i):
        doc = self.doc
        tok = doc[i]
        word = self.orig(tok)
        sentence_text = self.text
        self.selected_index = i
        self.mark_selected(i)
        self.refresh_known_btn()
        self.conj_btn.configure(
            state="normal" if tok.pos_ in ("VERB", "AUX") else "disabled")
        grammar = [(line + "\n", None) for line in explain_token(tok)]
        self.set_info([(word + "\n", "h"), ("Translating...\n\n", "sub")] + grammar)
        self.save_btn.configure(state="normal")
        self.ask_btn.configure(state="normal")
        self.say_word_btn.configure(state="normal")

        lemma_differs = tok.lemma_.lower() != tok.text.lower()

        def work():
            word_en = self.analyzer.translate(word)
            lemma_en = self.analyzer.translate(tok.lemma_) if lemma_differs else None
            return word_en, lemma_en

        def done(res, err):
            if self.doc is not doc or self.selected_index != i:
                return  # user moved on
            parts = [(word + "\n", "h")]
            if err:
                parts.append((f"(Translation failed - check your internet. {err})\n", "sub"))
                word_en = ""
            else:
                word_en, lemma_en = res
                parts += [("English: ", "b"), (word_en + "\n", None)]
                if lemma_differs:
                    parts += [("Dictionary form: ", "b"), (f"{tok.lemma_} = {lemma_en}\n", None)]
            parts.append(("\n", None))
            parts += grammar
            self.set_info(parts)
            self.last_word = (word, tok.lemma_, word_en, sentence_text)

        self.run_bg(work, done)

    def translate_sentence(self):
        if not self.doc:
            self.set_status("Capture or paste some text first.")
            return
        text = self.text
        self.set_info([("Translating...", "sub")])

        def done(res, err):
            self.set_info([("Translation\n", "h"),
                           (res if not err else f"Translation failed: {err}", None)])

        self.run_bg(lambda: self.analyzer.translate(text), done)

    def explain_sentence(self):
        if not self.doc:
            self.set_status("Capture or paste some text first.")
            return
        doc, text = self.doc, self.text
        self.set_info([("Working on it...", "sub")])

        if has_claude():
            prompt = (
                "You are a friendly Spanish tutor. An English-speaking learner saw this line "
                f"in a video game: «{text}»\n\n"
                "Give: 1) a natural English translation, 2) a short word-by-word gloss, "
                "3) brief explanations of the key grammar points (verb tenses and why they're "
                "used, pronouns, gender/agreement, idioms). Plain text, no markdown, under 200 words."
            )

            def done(res, err):
                self.set_info([("Grammar explanation\n", "h"),
                               (res if not err else f"Claude request failed: {err}", None)])

            self.run_bg(lambda: ask_claude(prompt, self.cfg["claude_model"]), done)
            return

        def done(res, err):
            parts = [("Translation\n", "h"),
                     ((res if not err else "(translation unavailable)") + "\n\n", None),
                     ("Word by word\n", "h")]
            for tok in doc:
                if tok.is_alpha:
                    parts += [(self.orig(tok), "b"), (f" - {short_summary(tok)}\n", None)]
            parts.append(("\nTip: click a word for details. Add an Anthropic API key for "
                          "tutor-style explanations (see README).", "sub"))
            self.set_info(parts)

        self.run_bg(lambda: self.analyzer.translate(text), done)

    def ask_about_word(self):
        if self.selected_index is None or not self.doc:
            return
        if not has_claude():
            messagebox.showinfo("Claude not set up",
                                "Add an Anthropic API key to use this. See README.md.")
            return
        word = self.orig(self.doc[self.selected_index])
        prompt = (
            f"In the Spanish sentence «{self.text}», explain the word «{word}» to an "
            "English-speaking learner: its meaning here, its dictionary form, its grammar "
            "(tense/person/gender etc.), and one simple extra example sentence with translation. "
            "Plain text, under 120 words."
        )
        self.set_info([(word + "\n", "h"), ("Asking Claude...", "sub")])

        def done(res, err):
            self.set_info([(word + "\n", "h"),
                           (res if not err else f"Claude request failed: {err}", None)])

        self.run_bg(lambda: ask_claude(prompt, self.cfg["claude_model"]), done)

    # ---------- conjugation ----------
    def show_conjugation(self):
        """Open the table for the selected verb, loading verbecc if needed."""
        if self.selected_index is None or not self.doc:
            return
        tok = self.doc[self.selected_index]
        if tok.pos_ not in ("VERB", "AUX"):
            self.set_status("Pick a verb to see a conjugation table.")
            return
        infinitive = (tok.lemma_ or tok.text).strip()
        clicked = self.orig(tok)
        warm = self.conjugator.engine is not None
        self.set_status(f"Conjugating '{infinitive}'..." if warm else
                        "Starting the conjugator - the first time takes a moment...")

        def done(res, err):
            if err:
                name = type(err).__name__
                if "VerbNotFound" in name:
                    self.set_status(f"'{infinitive}' isn't a verb the conjugator knows.")
                elif isinstance(err, ImportError):
                    self.set_status("The conjugator isn't installed - run setup.bat again.")
                else:
                    self.set_status(f"Conjugation failed: {err}")
                return
            data, english = res
            ConjugationWindow(self, data, clicked, english)
            self.set_status(f"Conjugation of '{infinitive}'.")

        def work():
            found, data = resolve_infinitive(self.conjugator, clicked, infinitive)
            if data is None:
                # Nothing matched, so fall back to spaCy's guess and let the
                # window say the forms were predicted.
                found, data = infinitive, self.conjugator.conjugate(infinitive)
            try:
                english = self.analyzer.translate(found)
            except Exception:  # noqa: BLE001
                english = ""
            return data, english

        self.run_bg(work, done)

    # ---------- known words ----------
    def refresh_known_btn(self):
        if self.selected_index is None or not self.doc:
            self.known_btn.configure(state="disabled", text="Mark known")
            return
        known = self.word_state(self.doc[self.selected_index]) == "known"
        self.known_btn.configure(state="normal",
                                 text="Unmark known" if known else "Mark known")

    def toggle_known(self):
        """Mark the selected word as one you already know, or undo that."""
        if self.selected_index is None or not self.doc:
            return
        tok = self.doc[self.selected_index]
        lemma = (tok.lemma_ or tok.text).strip()
        surface = self.orig(tok)
        keys = {lemma.lower(), surface.strip().lower()} - {""}

        if keys & self.known_forms:
            for key in list(self.known):
                entry_forms = set((self.known[key].get("forms") or "").lower().split())
                if key in keys or keys & entry_forms:
                    self.known.pop(key)
            self.set_status(f"'{lemma}' counts as new again.")
        else:
            self.known[lemma.lower()] = {"dictionary_form": lemma, "seen_as": surface,
                                         "added": today().isoformat(),
                                         "forms": " ".join(sorted(keys))}
            self.set_status(f"Marked '{lemma}' as known - it won't be highlighted now.")
            if tok.pos_ in ("VERB", "AUX"):
                self.learn_verb_forms(lemma, surface)
            self.offer_to_drop_card(lemma, keys)
        self.rebuild_known_forms()
        self.persist_known()
        self.render_sentence()
        self.refresh_known_btn()

    def persist_known(self):
        try:
            save_known(self.known)
        except OSError as e:  # noqa: BLE001
            self.set_status(f"Could not write known.csv: {e}")

    def learn_verb_forms(self, lemma, surface):
        """Knowing a verb means knowing its conjugations, so fetch them all.

        Runs in the background: the first call has to start the conjugator.
        """
        key = lemma.lower()

        def done(res, err):
            if err or not res or key not in self.known:
                return
            infinitive, forms = res
            entry = self.known.pop(key)
            entry["dictionary_form"] = infinitive or entry["dictionary_form"]
            entry["forms"] = " ".join(sorted(forms))
            self.known[(infinitive or key).lower()] = entry
            self.rebuild_known_forms()
            self.persist_known()
            if self.doc:
                self.render_sentence()
                self.refresh_known_btn()

        def work():
            infinitive, data = resolve_infinitive(self.conjugator, surface, lemma)
            if not data:
                return None
            return infinitive, simple_forms(data) | {surface.lower(), key}

        self.run_bg(work, done)

    def offer_to_drop_card(self, lemma, keys):
        """A word you know needn't keep coming up in reviews."""
        cards = [c for c in self.vocab
                 if {(c.get("spanish") or "").strip().lower(),
                     (c.get("dictionary_form") or "").strip().lower()} & keys]
        if not cards:
            return
        if not messagebox.askyesno(
                "Stop reviewing it?",
                f"'{lemma}' is in your review deck as well.\n\n"
                "Take it out, so it stops coming up?"):
            return
        self.vocab[:] = [c for c in self.vocab if c not in cards]
        try:
            save_vocab(self.vocab)
        except OSError as e:  # noqa: BLE001
            self.set_status(f"Could not write vocab.csv: {e}")
        self.refresh_due()

    # ---------- speech ----------
    def say_sentence(self):
        if not self.text:
            self.set_status("Capture or paste some text first.")
            return
        self.say(self.text)

    def say_word(self):
        if self.selected_index is None or not self.doc:
            return
        self.say(self.orig(self.doc[self.selected_index]))

    def say(self, text):
        """Read `text` aloud, cutting off whatever was playing before."""
        self.speaker.stop()
        self.speaker.turn += 1
        turn = self.speaker.turn
        self.set_status(f"Speaking: {text[:60]}")

        def done(res, err):
            if turn != self.speaker.turn:
                return  # a newer click has taken over
            if isinstance(err, NoSpanishVoice):
                self.offer_voice_setup(err.voices)
            elif err:
                self.set_status(f"Couldn't read that aloud: {err}")
            else:
                path, voice = res
                self.speaker.play(path)
                self.set_status(f"Reading aloud with {voice[0]} ({voice[1]}).")

        self.run_bg(lambda: self.speaker.render(text), done)

    def offer_voice_setup(self, voices):
        """No Spanish voice on this PC - explain how to add one."""
        self.set_status("No Spanish voice installed on Windows yet.")
        installed = ", ".join(f"{n} ({lang})" for n, lang, _ in voices) or "none"
        if messagebox.askyesno(
                "No Spanish voice installed",
                "Windows has no Spanish voice to read with, and reading Spanish "
                "with an English voice would teach you the wrong sounds.\n\n"
                f"Voices installed now: {installed}\n\n"
                "To add one: Settings > Time & language > Speech > Manage voices "
                "> Add voices > choose a Spanish voice, then restart this app.\n\n"
                "Open Windows speech settings now?"):
            try:
                os.startfile("ms-settings:speech")
            except OSError:
                self.set_status("Open Settings > Time & language > Speech to add a voice.")

    # ---------- vocab ----------
    def save_word(self):
        if not self.last_word:
            self.set_status("Wait for the translation to load, then save.")
            return
        word, lemma, english, sentence = self.last_word
        for card in self.vocab:
            if (card["spanish"].lower() == word.lower()
                    and card["sentence"].strip() == sentence.strip()):
                self.set_status(f"'{word}' is already in your deck "
                                f"(next review {card['due']}).")
                return
        self.vocab.append(new_card(word, lemma, english, sentence))
        try:
            save_vocab(self.vocab)
        except OSError as e:  # noqa: BLE001
            self.set_status(f"Could not write vocab.csv: {e}")
            return
        self.refresh_due()
        self.set_status(f"Saved '{word}' - it's in today's review.")

    def refresh_due(self):
        """Keep the Review button showing how many cards are waiting."""
        n = len(due_cards(self.vocab))
        self.review_btn.configure(text=f"Review ({n} due)" if n else "Review")

    def open_review(self):
        if self.review_win is not None and self.review_win.winfo_exists():
            self.review_win.lift()
            self.review_win.focus_force()
            return
        if not self.vocab:
            self.set_status("No saved words yet - click a word, then 'Save word'.")
            return
        self.review_win = ReviewWindow(self)

    def show_vocab(self):
        win = tk.Toplevel(self.root)
        win.title("My vocabulary")
        win.geometry("760x440")
        win.attributes("-topmost", self.cfg["always_on_top"])
        book = ttk.Notebook(win)
        book.pack(fill="both", expand=True)

        deck = ttk.Frame(book)
        book.add(deck, text=f"Review deck ({len(self.vocab)})")
        cols = ("spanish", "dictionary_form", "english", "next_review",
                "reviews", "sentence")
        tree = ttk.Treeview(deck, columns=cols, show="headings")
        for c, width in zip(cols, (100, 110, 130, 95, 60, 260)):
            tree.heading(c, text=c.replace("_", " ").title())
            tree.column(c, width=width)
        tree.pack(fill="both", expand=True)
        ttk.Button(deck, text="Review due words", command=self.open_review).pack(pady=6)
        stamp = today().isoformat()
        for card in sorted(self.vocab, key=lambda c: c.get("due") or ""):
            due = card.get("due") or ""
            tree.insert("", "end", values=(
                card["spanish"], card["dictionary_form"], card["english"],
                "due now" if due <= stamp else due, card.get("reps", "0"),
                card["sentence"]))
        if not self.vocab:
            tree.insert("", "end", values=("(no words saved yet)", "", "", "", "", ""))

        page = ttk.Frame(book)
        book.add(page, text=f"Known words ({len(self.known)})")
        self.build_known_tab(page, book)

    def build_known_tab(self, page, book):
        """Words marked as already known, with a way to take one back."""
        for child in page.winfo_children():
            child.destroy()
        cols = ("dictionary_form", "seen_as", "added")
        tree = ttk.Treeview(page, columns=cols, show="headings")
        for c, width in zip(cols, (200, 200, 120)):
            tree.heading(c, text=c.replace("_", " ").title())
            tree.column(c, width=width)
        tree.pack(fill="both", expand=True)
        for entry in sorted(self.known.values(),
                            key=lambda e: e["dictionary_form"].lower()):
            tree.insert("", "end", iid=entry["dictionary_form"].lower(),
                        values=(entry["dictionary_form"], entry.get("seen_as", ""),
                                entry.get("added", "")))
        if not self.known:
            tree.insert("", "end", values=("(nothing marked known yet)", "", ""))

        row = ttk.Frame(page, padding=(0, 6))
        row.pack(fill="x")

        def forget():
            for key in tree.selection():
                self.known.pop(key, None)
            try:
                save_known(self.known)
            except OSError as e:  # noqa: BLE001
                self.set_status(f"Could not write known.csv: {e}")
            if self.doc:
                self.render_sentence()
                self.refresh_known_btn()
            book.tab(1, text=f"Known words ({len(self.known)})")
            self.build_known_tab(page, book)

        ttk.Button(row, text="Treat as new again", command=forget).pack(side="left")
        ttk.Label(row, foreground="#888", text="  Pick a word, then click to undo it."
                  ).pack(side="left")

    def on_close(self):
        self.auto.stop()
        self.speaker.cleanup()
        save_config(self.cfg)
        try:
            import keyboard
            keyboard.unhook_all()
        except Exception:
            pass
        self.root.destroy()


if __name__ == "__main__":
    root = tk.Tk()
    App(root)
    root.mainloop()
