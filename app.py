#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Telegram Bot Hosting Manager  -  single file (app.py)
=====================================================

A Telegram bot that hosts other Python projects for its users:
upload ZIP -> per-project virtualenv -> sandboxed background process ->
live logs, stdin console, pip manager, file manager, server status.

Sections (search for the "# ====" banners):
  1. Configuration          6. Process manager        11. Telegram UI helpers
  2. Utilities              7. Log manager            12. Telegram handlers
  3. Database               8. Package manager        13. Admin commands
  4. Safe ZIP extraction    9. File manager helpers   14. Background monitor
  5. Sandbox + Projects    10. Resource monitoring    15. Main startup

Runs on Linux only (named pipes, process groups, Docker). Python 3.9+.
All configuration comes from environment variables / a .env file.
"""
from __future__ import annotations

import asyncio
import errno
import html
import logging
import os
import re
import shlex
import shutil
import signal
import sqlite3
import stat
import subprocess
import sys
import threading
import time
import zipfile
from pathlib import Path
from typing import Any, Awaitable, Callable, Optional

try:
    import psutil
except ImportError:  # pragma: no cover
    sys.exit("Missing dependency 'psutil'. Run: pip install -r requirements.txt")

try:
    from telegram import (InlineKeyboardButton, InlineKeyboardMarkup, Message,
                          Update, BotCommand)
    from telegram.constants import ParseMode
    from telegram.error import BadRequest, InvalidToken, RetryAfter, TelegramError
    from telegram.ext import (Application, CallbackQueryHandler, CommandHandler,
                              ContextTypes, MessageHandler, filters)
except ImportError:  # pragma: no cover
    sys.exit("Missing dependency 'python-telegram-bot'. Run: pip install -r requirements.txt")

try:
    from cryptography.fernet import Fernet, InvalidToken as FernetInvalid
except ImportError:  # optional: secrets are then stored unencrypted
    Fernet = None  # type: ignore
    FernetInvalid = Exception  # type: ignore

__version__ = "2.0.0"
log = logging.getLogger("hostmgr")
BASE_DIR = Path(__file__).resolve().parent
HTML = ParseMode.HTML


# ============================================================================
# 1. CONFIGURATION
# ============================================================================
def load_env_file(path: Path) -> None:
    """Minimal .env loader (does not override variables already set)."""
    try:
        for raw in path.read_text(encoding="utf-8").splitlines():
            line = raw.strip()
            if not line or line.startswith("#") or "=" not in line:
                continue
            k, v = line.split("=", 1)
            k, v = k.strip(), v.strip().strip('"').strip("'")
            os.environ.setdefault(k, v)
    except FileNotFoundError:
        pass


def _truthy(v: str) -> bool:
    return str(v).strip().lower() in ("1", "true", "yes", "on")


def _int(name: str, default: int) -> int:
    try:
        return int(os.environ.get(name, default))
    except ValueError:
        return default


def _float(name: str, default: float) -> float:
    try:
        return float(os.environ.get(name, default))
    except ValueError:
        return default


class Config:
    def __init__(self) -> None:
        e = os.environ.get
        self.bot_token = (e("BOT_TOKEN") or "").strip()
        ids = e("ADMIN_IDS") or e("ADMIN_ID") or ""
        self.admin_ids = {int(x) for x in re.findall(r"\d+", ids)}
        self.allowed_users = {int(x) for x in re.findall(r"\d+", e("ALLOWED_USERS") or "")}
        self.allow_public = _truthy(e("ALLOW_PUBLIC", "false"))
        self.data_dir = Path(e("DATA_DIR") or (BASE_DIR / "data")).resolve()
        # Sandbox: "docker" (recommended) or "process" (NOT isolated, admin use only)
        self.sandbox = (e("SANDBOX_MODE") or "docker").strip().lower()
        self.allow_unsandboxed_users = _truthy(e("ALLOW_UNSANDBOXED_USERS", "false"))
        self.docker_bin = e("DOCKER_BIN") or "docker"
        self.docker_image = e("DOCKER_IMAGE") or "python:3.11-slim"
        self.docker_network = e("DOCKER_NETWORK") or "bridge"
        # Limits
        self.max_projects = _int("MAX_PROJECTS_PER_USER", 3)
        self.max_zip_mb = _int("MAX_ZIP_MB", 20)          # Bot API download cap is 20 MB
        self.max_unzipped_mb = _int("MAX_UNZIPPED_MB", 200)
        self.max_file_mb = _int("MAX_FILE_MB", 50)
        self.max_files = _int("MAX_ZIP_FILES", 5000)
        self.max_project_mb = _int("MAX_PROJECT_MB", 500)
        self.mem_mb = _int("PROJECT_MEM_MB", 512)
        self.cpus = _float("PROJECT_CPUS", 1.0)
        self.pids_limit = _int("PROJECT_PIDS", 256)
        self.pip_timeout = _int("PIP_TIMEOUT_SEC", 900)
        self.cmd_timeout = _int("INPUT_TIMEOUT_SEC", 120)
        self.live_interval = _float("LIVE_INTERVAL_SEC", 3.0)
        self.live_seconds = _int("LIVE_MAX_SEC", 300)
        self.max_log_mb = _int("MAX_LOG_MB", 20)
        self.auto_restart_max = _int("AUTO_RESTART_MAX", 10)
        self.auto_restart_default = _truthy(e("AUTO_RESTART_DEFAULT", "true"))   # keep-alive for new projects
        self.resume_on_start = _truthy(e("RESUME_ON_START", "true"))            # auto-run previously running bots
        self.auto_backup_hours = _int("AUTO_BACKUP_HOURS", 24)                  # 0 = off
        self.backup_keep = _int("BACKUPS_KEEP", 5)
        self.python_versions = [v.strip() for v in (e("PYTHON_VERSIONS") or "3.9,3.10,3.11,3.12,3.13").split(",")
                                if re.fullmatch(r"3\.\d{1,2}", v.strip())]
        self.monitor_interval = _float("MONITOR_INTERVAL_SEC", 5.0)
        self.encryption_key = (e("ENCRYPTION_KEY") or "").strip()
        # Directories (created at startup)
        self.d_projects = self.data_dir / "projects"
        self.d_venvs = self.data_dir / "venvs"
        self.d_logs = self.data_dir / "logs"
        self.d_runtime = self.data_dir / "runtime"
        self.d_backups = self.data_dir / "backups"
        self.d_tmp = self.data_dir / "tmp"
        self.db_path = self.data_dir / "hostmgr.sqlite3"

    def ensure_dirs(self) -> None:
        for d in (self.data_dir, self.d_projects, self.d_venvs, self.d_logs,
                  self.d_runtime, self.d_backups, self.d_tmp):
            d.mkdir(parents=True, exist_ok=True)
        for d in (self.data_dir, self.d_runtime, self.d_backups):
            try:
                os.chmod(d, 0o700)
            except OSError:
                pass


CFG: Config  # initialised in main()


def is_admin(uid: int) -> bool:
    return uid in CFG.admin_ids


# ============================================================================
# 2. UTILITIES
# ============================================================================
ANSI_RE = re.compile(r"\x1b\[[0-9;?]*[ -/]*[@-~]")
NAME_BAD = re.compile(r"[^A-Za-z0-9 _.\-]")
PKG_RE = re.compile(
    r"^[A-Za-z0-9][A-Za-z0-9._\-]*(\[[A-Za-z0-9,._\-]+\])?"
    r"((==|>=|<=|~=|!=|>|<)[A-Za-z0-9.*+!_\-]+)?$")
ENV_KEY_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]{0,39}$")
BLOCKED_ENV = {"PATH", "HOME", "PYTHONHOME", "PYTHONPATH", "PYTHONSTARTUP",
               "PYTHONUSERBASE", "VIRTUAL_ENV", "SHELL", "USER", "IFS"}
START_TIME = time.time()


def esc(s: Any) -> str:
    return html.escape(str(s), quote=False)


def bar(pct: float, n: int = 10) -> str:
    f = int(round(max(0.0, min(100.0, float(pct))) / 100 * n))
    return "▰" * f + "▱" * (n - f)


def py_version(p: Any) -> str:
    m = re.search(r"python:(\d+\.\d+)", (p["image"] or CFG.docker_image) or "")
    return m.group(1) if m else "default"


def strip_ansi(s: str) -> str:
    return ANSI_RE.sub("", s)


def human_bytes(n: float) -> str:
    n = float(n)
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if abs(n) < 1024 or unit == "TB":
            return f"{n:.0f} {unit}" if unit == "B" else f"{n:.1f} {unit}"
        n /= 1024
    return f"{n:.1f} TB"


def human_dur(sec: float) -> str:
    sec = int(max(0, sec))
    d, r = divmod(sec, 86400)
    h, r = divmod(r, 3600)
    m, s = divmod(r, 60)
    if d:
        return f"{d}d {h}h {m}m"
    if h:
        return f"{h}h {m}m {s}s"
    if m:
        return f"{m}m {s}s"
    return f"{s}s"


def ts_str(ts: Optional[float]) -> str:
    return time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(ts)) if ts else "-"


def clean_name(s: str, default: str = "project") -> str:
    s = NAME_BAD.sub("", s).strip(" .")[:40]
    return s or default


def valid_filename(name: str) -> bool:
    return bool(name) and name not in (".", "..") and not any(c in name for c in "/\\\x00") \
        and len(name) <= 120


def safe_join(base: Path, rel: str) -> Path:
    """Resolve `rel` inside `base`; raise ValueError if it escapes (symlinks included)."""
    base_r = Path(os.path.realpath(base))
    rel = (rel or "").replace("\\", "/").strip("/")
    if "\x00" in rel:
        raise ValueError("Invalid path")
    target = Path(os.path.realpath(base_r / rel)) if rel else base_r
    if target != base_r and base_r not in target.parents:
        raise ValueError("Path escapes the project directory")
    return target


def rel_of(base: Path, path: Path) -> str:
    r = os.path.relpath(path, os.path.realpath(base))
    return "" if r == "." else r.replace(os.sep, "/")


def fit_tail(lines: list[str], limit: int) -> tuple[str, int]:
    """Take the last lines that fit `limit` characters once HTML-escaped."""
    out: list[str] = []
    size = 0
    for line in reversed(lines):
        n = len(esc(line)) + 1
        if size + n > limit:
            if not out:
                keep = line[-limit:]
                while len(esc(keep)) > limit - 5:
                    keep = keep[len(keep) // 10 + 1:]
                out.append(keep)
            break
        out.append(line)
        size += n
    out.reverse()
    return "\n".join(out), len(out)


def read_text_file(path: Path, limit: int = 1_000_000) -> str:
    with open(path, "rb") as f:
        data = f.read(limit + 1)
    if len(data) > limit:
        raise ValueError(f"File is larger than {human_bytes(limit)}")
    if b"\x00" in data[:2048]:
        raise ValueError("Binary file")
    return data.decode("utf-8", "replace")


def atomic_write(path: Path, data: bytes) -> None:
    tmp = path.with_name(f".{path.name}.tmp{os.getpid()}")
    with open(tmp, "wb") as f:
        f.write(data)
    os.replace(tmp, path)


def dir_size(path: Path) -> int:
    total = 0
    for root, dirs, files in os.walk(path, followlinks=False):
        for f in files:
            try:
                total += os.lstat(os.path.join(root, f)).st_size
            except OSError:
                pass
    return total


async def run_exec(cmd: list[str], *, cwd: Optional[str] = None, env: Optional[dict] = None,
                   timeout: float = 60, on_output: Optional[Callable[[str], Awaitable[None]]] = None,
                   on_timeout: Optional[Callable[[], Awaitable[None]]] = None) -> tuple[int, str]:
    """Run a command (no shell), stream merged output, enforce timeout. Returns (rc, output)."""
    try:
        proc = await asyncio.create_subprocess_exec(
            *cmd, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.STDOUT,
            stdin=asyncio.subprocess.DEVNULL, cwd=cwd, env=env,
            start_new_session=True, limit=2 ** 20)
    except OSError as e:
        return 127, f"Cannot execute {cmd[0]}: {e}"
    chunks: list[str] = []
    last = 0.0

    async def reader() -> None:
        nonlocal last
        assert proc.stdout is not None
        while True:
            line = await proc.stdout.readline()
            if not line:
                break
            chunks.append(line.decode("utf-8", "replace").replace("\r", "\n").rstrip("\n"))
            if on_output and time.time() - last > 2.0:
                last = time.time()
                try:
                    await on_output("\n".join(chunks))
                except Exception:
                    pass
        await proc.wait()

    try:
        await asyncio.wait_for(reader(), timeout=timeout)
    except asyncio.TimeoutError:
        if on_timeout:
            try:
                await on_timeout()
            except Exception:
                pass
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except OSError:
            pass
        chunks.append(f"[manager] TIMEOUT after {int(timeout)}s - command killed")
        return 124, "\n".join(chunks)
    return proc.returncode if proc.returncode is not None else -1, "\n".join(chunks)


# ============================================================================
# 3. DATABASE
# ============================================================================
class Secrets:
    """Fernet encryption for stored env vars / console history (if `cryptography` is present)."""

    def __init__(self) -> None:
        self.f = None
        if Fernet is None:
            log.warning("'cryptography' not installed - secrets are stored UNENCRYPTED")
            return
        key = CFG.encryption_key
        keyfile = CFG.data_dir / "secret.key"
        if not key:
            if keyfile.exists():
                key = keyfile.read_text().strip()
            else:
                key = Fernet.generate_key().decode()
                fd = os.open(keyfile, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
                with os.fdopen(fd, "w") as fh:
                    fh.write(key)
        try:
            self.f = Fernet(key.encode())
        except Exception:
            sys.exit("ENCRYPTION_KEY is invalid. Generate one with: "
                     "python -c \"from cryptography.fernet import Fernet;print(Fernet.generate_key().decode())\"")

    def enc(self, s: str) -> str:
        return "enc:" + self.f.encrypt(s.encode()).decode() if self.f else s

    def dec(self, s: str) -> str:
        if s.startswith("enc:") and self.f:
            try:
                return self.f.decrypt(s[4:].encode()).decode()
            except FernetInvalid:
                return ""
        return s


SCHEMA = """
CREATE TABLE IF NOT EXISTS users(
  id INTEGER PRIMARY KEY, username TEXT, first_seen REAL,
  approved INTEGER DEFAULT 0, banned INTEGER DEFAULT 0, max_projects INTEGER);
CREATE TABLE IF NOT EXISTS projects(
  id INTEGER PRIMARY KEY AUTOINCREMENT, owner_id INTEGER NOT NULL, name TEXT NOT NULL,
  startup TEXT, status TEXT DEFAULT 'new', pid INTEGER, pid_ctime REAL, container TEXT,
  started_at REAL, ended_at REAL, exit_code INTEGER, auto_restart INTEGER DEFAULT 0,
  restart_count INTEGER DEFAULT 0, created_at REAL, sandbox TEXT);
CREATE TABLE IF NOT EXISTS env_vars(
  project_id INTEGER, key TEXT, value TEXT, PRIMARY KEY(project_id, key));
CREATE TABLE IF NOT EXISTS cmd_history(
  id INTEGER PRIMARY KEY AUTOINCREMENT, project_id INTEGER, ts REAL, text TEXT);
CREATE INDEX IF NOT EXISTS idx_proj_owner ON projects(owner_id);
"""
PROJECT_COLS = {"name", "startup", "status", "pid", "pid_ctime", "container", "started_at",
                "ended_at", "exit_code", "auto_restart", "restart_count", "sandbox", "desired", "args", "image",
                "crash_count", "total_restarts", "restart_every_h"}


class Database:
    def __init__(self, path: Path) -> None:
        self.conn = sqlite3.connect(str(path), check_same_thread=False, isolation_level=None)
        self.conn.row_factory = sqlite3.Row
        self.lock = threading.RLock()
        with self.lock:
            self.conn.execute("PRAGMA journal_mode=WAL")
            self.conn.executescript(SCHEMA)
            self._migrate()
        try:
            os.chmod(path, 0o600)
        except OSError:
            pass

    def _migrate(self) -> None:
        """Add v2 columns to databases created by older versions (data is kept)."""
        cols = {r["name"] for r in self.conn.execute("PRAGMA table_info(projects)").fetchall()}
        fresh_desired = "desired" not in cols
        for name, ddl in (("desired", "INTEGER DEFAULT 0"), ("args", "TEXT"), ("image", "TEXT"),
                          ("crash_count", "INTEGER DEFAULT 0"), ("total_restarts", "INTEGER DEFAULT 0"),
                          ("restart_every_h", "INTEGER DEFAULT 0")):
            if name not in cols:
                self.conn.execute(f"ALTER TABLE projects ADD COLUMN {name} {ddl}")
        if fresh_desired:  # projects running under v1 should be resumed by v2
            self.conn.execute("UPDATE projects SET desired=1 WHERE status='running'")

    def q(self, sql: str, args: tuple = ()) -> list[sqlite3.Row]:
        with self.lock:
            return self.conn.execute(sql, args).fetchall()

    def one(self, sql: str, args: tuple = ()) -> Optional[sqlite3.Row]:
        with self.lock:
            return self.conn.execute(sql, args).fetchone()

    def x(self, sql: str, args: tuple = ()) -> int:
        with self.lock:
            return self.conn.execute(sql, args).lastrowid or 0

    # ---- users ----
    def touch_user(self, uid: int, username: Optional[str]) -> sqlite3.Row:
        approved = 1 if (is_admin(uid) or uid in CFG.allowed_users or CFG.allow_public) else 0
        self.x("INSERT OR IGNORE INTO users(id,username,first_seen,approved) VALUES(?,?,?,?)",
               (uid, username, time.time(), approved))
        if username:
            self.x("UPDATE users SET username=? WHERE id=?", (username, uid))
        if approved:
            self.x("UPDATE users SET approved=1 WHERE id=? AND banned=0 AND approved=0", (uid,))
        return self.one("SELECT * FROM users WHERE id=?", (uid,))  # type: ignore

    def user(self, uid: int) -> Optional[sqlite3.Row]:
        return self.one("SELECT * FROM users WHERE id=?", (uid,))

    def users(self) -> list[sqlite3.Row]:
        return self.q("SELECT * FROM users ORDER BY first_seen")

    def set_user(self, uid: int, **kw: Any) -> None:
        for k, v in kw.items():
            if k in ("approved", "banned", "max_projects"):
                self.x(f"UPDATE users SET {k}=? WHERE id=?", (v, uid))

    # ---- projects ----
    def add_project(self, owner: int, name: str, sandbox: str) -> int:
        return self.x("INSERT INTO projects(owner_id,name,created_at,sandbox,auto_restart) VALUES(?,?,?,?,?)",
                      (owner, name, time.time(), sandbox, 1 if CFG.auto_restart_default else 0))

    def project(self, pid: int) -> Optional[sqlite3.Row]:
        return self.one("SELECT * FROM projects WHERE id=?", (pid,))

    def projects_of(self, owner: int) -> list[sqlite3.Row]:
        return self.q("SELECT * FROM projects WHERE owner_id=? ORDER BY id", (owner,))

    def all_projects(self) -> list[sqlite3.Row]:
        return self.q("SELECT * FROM projects ORDER BY id")

    def projects_by_status(self, status: str) -> list[sqlite3.Row]:
        return self.q("SELECT * FROM projects WHERE status=?", (status,))

    def update_project(self, _id: int, **kw: Any) -> None:
        kw = {k: v for k, v in kw.items() if k in PROJECT_COLS}
        if kw:
            sets = ",".join(f"{k}=?" for k in kw)
            self.x(f"UPDATE projects SET {sets} WHERE id=?", (*kw.values(), _id))

    def delete_project(self, pid: int) -> None:
        for t in ("env_vars", "cmd_history"):
            self.x(f"DELETE FROM {t} WHERE project_id=?", (pid,))
        self.x("DELETE FROM projects WHERE id=?", (pid,))

    def count_projects(self, owner: int) -> int:
        return self.one("SELECT COUNT(*) c FROM projects WHERE owner_id=?", (owner,))["c"]  # type: ignore

    # ---- env vars (encrypted) ----
    def env_get(self, pid: int) -> dict[str, str]:
        return {r["key"]: SECRETS.dec(r["value"])
                for r in self.q("SELECT key,value FROM env_vars WHERE project_id=? ORDER BY key", (pid,))}

    def env_set(self, pid: int, key: str, value: str) -> None:
        self.x("INSERT OR REPLACE INTO env_vars(project_id,key,value) VALUES(?,?,?)",
               (pid, key, SECRETS.enc(value)))

    def env_del(self, pid: int, key: str) -> None:
        self.x("DELETE FROM env_vars WHERE project_id=? AND key=?", (pid, key))

    # ---- console history ----
    def hist_add(self, pid: int, text: str) -> None:
        for r in self.q("SELECT id,text FROM cmd_history WHERE project_id=? ORDER BY id DESC LIMIT 30", (pid,)):
            if SECRETS.dec(r["text"]) == text:
                self.x("DELETE FROM cmd_history WHERE id=?", (r["id"],))
        self.x("INSERT INTO cmd_history(project_id,ts,text) VALUES(?,?,?)", (pid, time.time(), SECRETS.enc(text)))
        self.x("DELETE FROM cmd_history WHERE project_id=? AND id NOT IN "
               "(SELECT id FROM cmd_history WHERE project_id=? ORDER BY id DESC LIMIT 50)", (pid, pid))

    def hist_list(self, pid: int, n: int = 10) -> list[tuple[int, str]]:
        return [(r["id"], SECRETS.dec(r["text"])) for r in
                self.q("SELECT id,text FROM cmd_history WHERE project_id=? ORDER BY id DESC LIMIT ?", (pid, n))]

    def hist_get(self, hid: int) -> Optional[tuple[int, str]]:
        r = self.one("SELECT project_id,text FROM cmd_history WHERE id=?", (hid,))
        return (r["project_id"], SECRETS.dec(r["text"])) if r else None


DB: Database
SECRETS: Secrets


# ============================================================================
# 4. SAFE ZIP EXTRACTION
# ============================================================================
class ZipError(Exception):
    pass


def safe_extract(zip_path: Path, dest: Path, progress: dict, *, strip_top: bool = True,
                 keep: Optional[Callable[[list], bool]] = None) -> int:
    """Extract a ZIP defensively (blocking; run in an executor).

    Rejects: absolute paths, '..', drive letters, encrypted members, zip bombs
    (limits on count / per-file / total size, enforced on bytes ACTUALLY written).
    Skips: symlinks and special files.  Returns number of files written.
    """
    max_total = CFG.max_unzipped_mb * 1048576
    max_file = CFG.max_file_mb * 1048576
    try:
        zf = zipfile.ZipFile(zip_path)
    except zipfile.BadZipFile:
        raise ZipError("Not a valid ZIP archive")
    with zf:
        infos = [i for i in zf.infolist() if not i.filename.startswith("__MACOSX/")
                 and os.path.basename(i.filename.rstrip("/")) != ".DS_Store"]
        if not infos:
            raise ZipError("The archive is empty")
        if len(infos) > CFG.max_files:
            raise ZipError(f"Too many entries ({len(infos)} > {CFG.max_files})")
        if sum(i.file_size for i in infos) > max_total:
            raise ZipError(f"Uncompressed size exceeds {CFG.max_unzipped_mb} MB")
        names = [i.filename.replace("\\", "/") for i in infos]
        prefix = ""
        if strip_top:
            tops = {n.split("/")[0] for n in names if n}
            if len(tops) == 1:
                top = next(iter(tops))
                if all(n == top + "/" or n.startswith(top + "/") for n in names):
                    prefix = top + "/"
        dest.mkdir(parents=True, exist_ok=True)
        dest_r = Path(os.path.realpath(dest))
        progress["total"] = len(infos)
        total = written_files = 0
        for idx, info in enumerate(infos):
            progress["done"] = idx
            name = info.filename.replace("\\", "/")
            if info.flag_bits & 0x1:
                raise ZipError("Encrypted ZIP entries are not supported")
            if name.startswith("/") or "\x00" in name or re.match(r"^[A-Za-z]:", name):
                raise ZipError(f"Unsafe path in archive: {name!r}")
            parts = [p for p in name.split("/") if p not in ("", ".")]
            if ".." in parts:
                raise ZipError(f"Path traversal in archive: {name!r}")
            if prefix and name.startswith(prefix):
                parts = [p for p in name[len(prefix):].split("/") if p not in ("", ".")]
            if not parts:
                continue
            mode = (info.external_attr >> 16) & 0o170000
            if mode and mode not in (stat.S_IFREG, stat.S_IFDIR):
                progress["skipped"] = progress.get("skipped", 0) + 1  # symlink / device
                continue
            target = Path(os.path.realpath(dest_r.joinpath(*parts)))
            if target != dest_r and dest_r not in target.parents:
                raise ZipError(f"Unsafe path in archive: {name!r}")
            if info.is_dir():
                target.mkdir(parents=True, exist_ok=True)
                continue
            if keep and target.exists() and keep(parts):  # update mode: never overwrite user data
                progress["kept"] = progress.get("kept", 0) + 1
                continue
            target.parent.mkdir(parents=True, exist_ok=True)
            size = 0
            with zf.open(info) as src, open(target, "wb") as out:
                while True:
                    buf = src.read(65536)
                    if not buf:
                        break
                    size += len(buf)
                    total += len(buf)
                    if size > max_file or total > max_total:
                        raise ZipError("Archive exceeds the allowed extracted size (possible zip bomb)")
                    out.write(buf)
            os.chmod(target, 0o755 if (info.external_attr >> 16) & 0o111 else 0o644)
            written_files += 1
            progress["bytes"] = total
        progress["done"] = len(infos)
    return written_files


# ============================================================================
# 5. SANDBOX + PROJECT MANAGEMENT
# ============================================================================
EXIT_WRAPPER = 'ef="$1"; shift; "$@"; echo $? > "$ef"'
PREFERRED_STARTUP = ["app.py", "main.py", "bot.py", "run.py", "start.py", "index.py", "__main__.py"]
SKIP_DIRS = {"__pycache__", "node_modules", "venv", ".venv", "env", "site-packages", ".git"}


class Sandbox:
    """Builds the command lines that run hosted code, either inside a hardened
    Docker container (recommended) or - for admin testing - a plain subprocess."""

    def __init__(self) -> None:
        self.mode = CFG.sandbox

    @property
    def docker(self) -> bool:
        return self.mode == "docker"

    def check(self) -> tuple[bool, str]:
        if self.mode not in ("docker", "process"):
            return False, "SANDBOX_MODE must be 'docker' or 'process'."
        if self.docker:
            if not shutil.which(CFG.docker_bin):
                return False, ("Docker was not found. Install Docker (https://docs.docker.com/engine/install/) "
                               "and add this user to the 'docker' group, or set SANDBOX_MODE=process "
                               "(NOT isolated; admin testing only).")
            try:
                r = subprocess.run([CFG.docker_bin, "info", "--format", "{{.ServerVersion}}"],
                                   capture_output=True, text=True, timeout=30)
            except Exception as e:
                return False, f"Cannot talk to Docker: {e}"
            if r.returncode != 0:
                return False, "Docker daemon is not reachable: " + (r.stderr.strip()[:300] or "unknown error")
        elif hasattr(os, "getuid") and os.getuid() == 0:
            log.warning("Running unsandboxed projects as root is dangerous!")
        return True, "ok"

    # ---- paths ----
    def venv_host(self, p: sqlite3.Row) -> Path:
        return CFG.d_venvs / str(p["id"])

    def venv_python_host(self, p: sqlite3.Row) -> Path:
        return self.venv_host(p) / "bin" / "python"

    def image(self, p: sqlite3.Row) -> str:
        return p["image"] or CFG.docker_image

    def extra_args(self, p: sqlite3.Row) -> list[str]:
        try:
            return shlex.split(p["args"]) if p["args"] else []
        except ValueError:
            return []

    def container_name(self, p: sqlite3.Row) -> str:
        return f"tgh-{p['id']}"

    # ---- environments ----
    def _client_env(self) -> dict:
        drop = {"BOT_TOKEN", "ENCRYPTION_KEY", "ADMIN_IDS", "ADMIN_ID", "ALLOWED_USERS"}
        return {k: v for k, v in os.environ.items() if k not in drop}

    def _process_env(self, p: sqlite3.Row, extra: dict) -> dict:
        venv = self.venv_host(p)
        env = {"PATH": f"{venv}/bin:/usr/local/bin:/usr/bin:/bin", "HOME": str(PROJECTS.src_dir(p)),
               "LANG": "C.UTF-8", "PYTHONUNBUFFERED": "1", "VIRTUAL_ENV": str(venv)}
        env.update(extra)
        return env

    def _preexec(self) -> Callable[[], None]:
        mem = CFG.mem_mb * 1048576 * 4
        fsz = CFG.max_file_mb * 1048576 * 4

        def fn() -> None:
            import resource
            for lim, val in ((resource.RLIMIT_AS, mem), (resource.RLIMIT_FSIZE, fsz),
                             (resource.RLIMIT_NOFILE, 4096), (resource.RLIMIT_CORE, 0)):
                try:
                    resource.setrlimit(lim, (val, val))
                except (ValueError, OSError):
                    pass
        return fn

    # ---- docker ----
    def _docker_base(self, p: sqlite3.Row, *, name: Optional[str], interactive: bool, venv_rw: bool,
                     envfile: Optional[Path] = None, tmp_size: str = "256m") -> list[str]:
        uid = os.getuid() if hasattr(os, "getuid") else 1000
        gid = os.getgid() if hasattr(os, "getgid") else 1000
        a = [CFG.docker_bin, "run", "--rm"]
        if interactive:
            a.append("-i")
        if name:
            a += ["--name", name]
        a += ["--label", "tgh=1", "--user", f"{uid}:{gid}",
              "--memory", f"{CFG.mem_mb}m", "--memory-swap", f"{CFG.mem_mb}m",
              "--cpus", str(CFG.cpus), "--pids-limit", str(CFG.pids_limit),
              "--cap-drop", "ALL", "--security-opt", "no-new-privileges",
              "--read-only", "--tmpfs", f"/tmp:rw,size={tmp_size},mode=1777",
              "--network", CFG.docker_network,
              "-e", "HOME=/tmp", "-e", "PYTHONUNBUFFERED=1", "-e", "PIP_DISABLE_PIP_VERSION_CHECK=1",
              "-v", f"{PROJECTS.src_dir(p)}:/app", "-v", f"{self.venv_host(p)}:/venv{'' if venv_rw else ':ro'}",
              "-w", "/app"]
        if envfile:
            a += ["--env-file", str(envfile)]
        return a

    # ---- public builders ----
    def build_run(self, p: sqlite3.Row, envvars: dict) -> tuple[list[str], dict, Optional[Callable], Optional[Path]]:
        startup = p["startup"]
        exitf = str(PROJECTS.exit_path(p))
        if self.docker:
            envfile = None
            if envvars:
                envfile = CFG.d_runtime / f"{p['id']}.env"
                fd = os.open(envfile, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
                with os.fdopen(fd, "w") as fh:
                    for k, v in envvars.items():
                        fh.write(f"{k}={v}\n")
            argv = self._docker_base(p, name=self.container_name(p), interactive=True, venv_rw=False,
                                     envfile=envfile) + [self.image(p), "/venv/bin/python", "-u", f"/app/{startup}", *self.extra_args(p)]
            return ["/bin/sh", "-c", EXIT_WRAPPER, "sh", exitf] + argv, self._client_env(), None, envfile
        argv = [str(self.venv_python_host(p)), "-u", startup, *self.extra_args(p)]
        return (["/bin/sh", "-c", EXIT_WRAPPER, "sh", exitf] + argv,
                self._process_env(p, envvars), self._preexec(), None)

    def build_pip(self, p: sqlite3.Row, args: list[str]) -> tuple[list[str], dict, Optional[str]]:
        if self.docker:
            name = f"tghpip-{p['id']}-{int(time.time())}"
            cmd = self._docker_base(p, name=name, interactive=False, venv_rw=True, tmp_size="1g") + \
                [self.image(p), "/venv/bin/python", "-m", "pip", *args, "--disable-pip-version-check"]
            return cmd, self._client_env(), name
        return ([str(self.venv_python_host(p)), "-m", "pip", *args, "--disable-pip-version-check"],
                self._process_env(p, {}), None)

    def build_venv(self, p: sqlite3.Row) -> tuple[list[str], dict]:
        if self.docker:
            cmd = self._docker_base(p, name=None, interactive=False, venv_rw=True, tmp_size="256m") + \
                [self.image(p), "python", "-m", "venv", "/venv"]
            return cmd, self._client_env()
        return [sys.executable, "-m", "venv", str(self.venv_host(p))], self._process_env(p, {})


class Projects:
    """Project records + on-disk layout (per-user isolation: projects/<owner>/<id>)."""

    def src_dir(self, p: sqlite3.Row) -> Path:
        return CFG.d_projects / str(p["owner_id"]) / str(p["id"])

    def exit_path(self, p: sqlite3.Row) -> Path:
        return CFG.d_runtime / f"{p['id']}.exit"

    def fifo_path(self, p: sqlite3.Row) -> Path:
        return CFG.d_runtime / f"{p['id']}.stdin"

    def log_path(self, p: sqlite3.Row) -> Path:
        return CFG.d_logs / f"{p['id']}.log"

    def user_limit(self, user: sqlite3.Row) -> int:
        if is_admin(user["id"]):
            return 10 ** 6
        return user["max_projects"] if user["max_projects"] is not None else CFG.max_projects

    def unique_name(self, owner: int, name: str) -> str:
        existing = {r["name"] for r in DB.projects_of(owner)}
        if name not in existing:
            return name
        i = 2
        while f"{name}-{i}" in existing:
            i += 1
        return f"{name}-{i}"

    def create(self, owner: int, name: str) -> sqlite3.Row:
        pid = DB.add_project(owner, name, SANDBOX.mode)
        p = DB.project(pid)
        assert p is not None
        self.src_dir(p).mkdir(parents=True, exist_ok=True)
        return p

    @staticmethod
    def list_py_files(src: Path, limit: int = 40) -> list[str]:
        out: list[str] = []
        base = Path(os.path.realpath(src))
        for root, dirs, files in os.walk(base, followlinks=False):
            dirs[:] = sorted(d for d in dirs if d not in SKIP_DIRS and not d.startswith("."))
            depth = 0 if Path(root) == base else len(Path(root).relative_to(base).parts)
            if depth > 3:
                dirs[:] = []
                continue
            for f in sorted(files):
                if f.endswith(".py"):
                    out.append(rel_of(base, Path(root) / f))
        out.sort(key=lambda r: (r.count("/"), r))
        return out[:limit]

    def detect_startup(self, src: Path) -> Optional[str]:
        for n in PREFERRED_STARTUP:
            if (src / n).is_file():
                return n
        root_py = [f for f in os.listdir(src) if f.endswith(".py") and (src / f).is_file()]
        return root_py[0] if len(root_py) == 1 else None

    def find_requirements(self, src: Path) -> Optional[str]:
        for cand in ("requirements.txt", "requirement.txt"):
            if (src / cand).is_file():
                return cand
        return None

    async def delete(self, p: sqlite3.Row) -> None:
        await PM.stop(p, force=True)
        src = self.src_dir(p)
        loop = asyncio.get_running_loop()
        if src.exists():  # backup before removal
            base = str(CFG.d_backups / f"{p['owner_id']}_{p['id']}_{int(time.time())}")
            try:
                await loop.run_in_executor(None, lambda: shutil.make_archive(base, "zip", str(src)))
            except Exception:
                log.exception("backup failed")
        await loop.run_in_executor(None, lambda: shutil.rmtree(src, ignore_errors=True))
        await loop.run_in_executor(None, lambda: shutil.rmtree(SANDBOX.venv_host(p), ignore_errors=True))
        for f in (self.log_path(p), self.log_path(p).with_suffix(".log.1"), self.exit_path(p),
                  self.fifo_path(p), CFG.d_runtime / f"{p['id']}.env"):
            try:
                f.unlink()
            except OSError:
                pass
        DB.delete_project(p["id"])

    def backup_files(self, p: sqlite3.Row) -> list[Path]:
        return sorted(CFG.d_backups.glob(f"{p['owner_id']}_{p['id']}_*.zip"), reverse=True)

    async def backup(self, p: sqlite3.Row) -> Optional[Path]:
        src = self.src_dir(p)
        if not src.exists():
            return None
        base = CFG.d_backups / f"{p['owner_id']}_{p['id']}_{int(time.time())}"
        try:
            await asyncio.get_running_loop().run_in_executor(
                None, lambda: shutil.make_archive(str(base), "zip", str(src)))
        except Exception:
            log.exception("backup failed")
            return None
        for old in self.backup_files(p)[CFG.backup_keep:]:
            old.unlink(missing_ok=True)
        return Path(str(base) + ".zip")

    async def restore(self, p: sqlite3.Row, zpath: Path) -> int:
        """Replace the project's files with a backup (extracted safely into a temp dir first)."""
        src = self.src_dir(p)
        tmpdir = CFG.d_tmp / f"restore_{p['id']}_{int(time.time())}"
        loop = asyncio.get_running_loop()
        try:
            n = await loop.run_in_executor(None, lambda: safe_extract(zpath, tmpdir, {}, strip_top=False))

            def swap() -> None:
                shutil.rmtree(src, ignore_errors=True)
                os.replace(tmpdir, src)
            await loop.run_in_executor(None, swap)
            return n
        finally:
            shutil.rmtree(tmpdir, ignore_errors=True)


SANDBOX: Sandbox
PROJECTS: Projects


# ============================================================================
# 7. LOG MANAGER   (defined before PM because PM uses it)
# ============================================================================
ERR_RE = re.compile(r"^\s*(?:[\w.]+\.)?\w*(?:Error|Exception|Exit|Interrupt)\b.*:|Traceback \(most recent")


class LogManager:
    def path(self, p: sqlite3.Row) -> Path:
        return PROJECTS.log_path(p)

    def marker(self, p: sqlite3.Row, msg: str) -> None:
        try:
            with open(self.path(p), "ab") as f:
                f.write(f"[manager {time.strftime('%Y-%m-%d %H:%M:%S')}] {msg}\n".encode())
        except OSError:
            pass

    def size(self, p: sqlite3.Row) -> int:
        try:
            return self.path(p).stat().st_size
        except OSError:
            return 0

    def tail_lines(self, p: sqlite3.Row, n: int, max_bytes: int = 4 * 1048576) -> list[str]:
        try:
            f = open(self.path(p), "rb")
        except OSError:
            return []
        with f:
            f.seek(0, 2)
            pos = f.tell()
            data = b""
            while pos > 0 and data.count(b"\n") <= n and len(data) < max_bytes:
                step = min(65536, pos)
                pos -= step
                f.seek(pos)
                data = f.read(step) + data
        lines = data.decode("utf-8", "replace").splitlines()
        if pos > 0 and lines:
            lines = lines[1:]
        return [strip_ansi(x) for x in lines[-n:]]

    def rotate_if_needed(self, p: sqlite3.Row) -> None:
        path = self.path(p)
        if self.size(p) > CFG.max_log_mb * 1048576:
            os.replace(path, path.with_suffix(".log.1"))

    def trim_running(self, p: sqlite3.Row) -> None:
        """Copy-truncate when a running project's log grows too large (child uses O_APPEND)."""
        path = self.path(p)
        if self.size(p) > CFG.max_log_mb * 2 * 1048576:
            try:
                with open(path, "rb") as f:
                    f.seek(-1048576, 2)
                    tail = f.read()
                shutil.copyfile(path, path.with_suffix(".log.1"))
                with open(path, "r+b") as f:
                    f.truncate(0)
                with open(path, "ab") as f:
                    f.write(b"[manager] log truncated (older part in .log.1 backup)\n" + tail)
            except OSError:
                pass

    def search(self, p: sqlite3.Row, query: str) -> list[str]:
        q = query.lower()
        return [l for l in self.tail_lines(p, 20000, 8 * 1048576) if q in l.lower()]

    def error_lines(self, p: sqlite3.Row) -> list[str]:
        pat = re.compile(r"Traceback|\b(ERROR|CRITICAL|FATAL)\b|^\s+File \"|" + ERR_RE.pattern)
        return [l for l in self.tail_lines(p, 20000, 8 * 1048576) if pat.search(l)]

    def last_error(self, p: sqlite3.Row) -> Optional[str]:
        for line in reversed(self.tail_lines(p, 300)):
            if ERR_RE.search(line) and not line.startswith("[manager"):
                return line.strip()[:200]
        return None


# ============================================================================
# 6. PROCESS MANAGER
# ============================================================================
def pid_alive(pid: Optional[int], ctime: Optional[float]) -> bool:
    if not pid:
        return False
    try:
        pr = psutil.Process(pid)
        if ctime and abs(pr.create_time() - ctime) > 1.5:
            return False  # PID was recycled by an unrelated process
        return pr.status() != psutil.STATUS_ZOMBIE
    except psutil.Error:
        return False


class ProcessManager:
    def __init__(self) -> None:
        self.popens: dict[int, subprocess.Popen] = {}
        self.locks: dict[int, asyncio.Lock] = {}
        self.pending: list[int] = []  # unexpected exits waiting for notification

    def lock(self, pid: int) -> asyncio.Lock:
        return self.locks.setdefault(pid, asyncio.Lock())

    def is_alive(self, p: sqlite3.Row) -> bool:
        po = self.popens.get(p["id"])
        if po is not None and po.pid == p["pid"]:
            return po.poll() is None
        return pid_alive(p["pid"], p["pid_ctime"])

    def fresh(self, pid: int) -> Optional[sqlite3.Row]:
        """Project row reconciled with the real process state."""
        p = DB.project(pid)
        if p and p["status"] == "running" and not self.is_alive(p):
            return self.finalize(pid)
        return p

    def uptime(self, p: sqlite3.Row) -> Optional[float]:
        if p["status"] == "running" and p["started_at"]:
            return time.time() - p["started_at"]
        return None

    def read_exit(self, p: sqlite3.Row) -> Optional[int]:
        try:
            return int(PROJECTS.exit_path(p).read_text().strip())
        except (OSError, ValueError):
            return None

    def finalize(self, pid: int, expected: bool = False, forced_code: Optional[int] = None,
                 notify: bool = True) -> Optional[sqlite3.Row]:
        p = DB.project(pid)
        if not p or p["status"] != "running":
            return p
        code = self.read_exit(p)
        po = self.popens.pop(pid, None)
        if code is None and po is not None and po.poll() is not None:
            code = po.returncode
        if code is None:
            code = forced_code
        status = "stopped" if (expected or code == 0) else "crashed"
        DB.update_project(pid, status=status, ended_at=time.time(), exit_code=code, pid=None, pid_ctime=None,
                          **({"desired": 0} if status == "stopped" else
                             {"crash_count": (p["crash_count"] or 0) + 1}))
        LOGS.marker(p, f"process {status}, exit code {code if code is not None else 'unknown'}")
        if not expected and notify:
            self.pending.append(pid)
        return DB.project(pid)

    async def _docker_cleanup(self, name: str) -> None:
        await run_exec([CFG.docker_bin, "rm", "-f", name], env=SANDBOX._client_env(), timeout=30)

    async def start(self, p: sqlite3.Row, progress: Optional[Callable[[str], Awaitable[None]]] = None,
                    manual: bool = True) -> tuple[bool, str]:
        async with self.lock(p["id"]):
            p = DB.project(p["id"])  # type: ignore
            if p is None:
                return False, "Project no longer exists."
            if self.is_alive(p):
                return False, "Project is already running."
            if p["status"] == "running":
                self.finalize(p["id"], notify=False)
                p = DB.project(p["id"])  # type: ignore
            if not p["startup"]:
                return False, "No startup file selected. Open Settings -> Startup file."
            if not SANDBOX.docker and not is_admin(p["owner_id"]) and not CFG.allow_unsandboxed_users:
                return False, ("Unsandboxed mode is enabled and only admins may run projects. "
                               "Ask the admin to enable Docker (SANDBOX_MODE=docker).")
            src = PROJECTS.src_dir(p)
            try:
                target = safe_join(src, p["startup"])
            except ValueError as e:
                return False, str(e)
            if not target.is_file():
                return False, f"Startup file not found: {p['startup']}"
            if progress:
                await progress("Preparing virtual environment...")
            ok, msg = await PKG.ensure_venv(p)
            if not ok:
                return False, "Could not create the virtualenv:\n" + msg
            if progress:
                await progress("Launching process...")
            if SANDBOX.docker:
                await self._docker_cleanup(SANDBOX.container_name(p))
            LOGS.rotate_if_needed(p)
            try:
                PROJECTS.exit_path(p).unlink()
            except OSError:
                pass
            fifo = PROJECTS.fifo_path(p)
            try:
                if fifo.exists() and not stat.S_ISFIFO(fifo.stat().st_mode):
                    fifo.unlink()
                if not fifo.exists():
                    os.mkfifo(fifo, 0o600)
            except OSError as e:
                return False, f"Cannot create stdin pipe: {e}"
            cmd, env, preexec, envfile = SANDBOX.build_run(p, DB.env_get(p["id"]))
            LOGS.marker(p, f"starting '{p['startup']}' (sandbox={SANDBOX.mode})")
            fd = os.open(fifo, os.O_RDWR)  # RDWR: never blocks, no EOF while child holds it
            logf = open(LOGS.path(p), "ab", buffering=0)
            try:
                proc = subprocess.Popen(cmd, stdin=fd, stdout=logf, stderr=subprocess.STDOUT,
                                        cwd=str(src), env=env, start_new_session=True,
                                        close_fds=True, preexec_fn=preexec)
            except OSError as e:
                LOGS.marker(p, f"failed to launch: {e}")
                return False, f"Failed to launch: {e}"
            finally:
                os.close(fd)
                logf.close()
            try:
                ctime = psutil.Process(proc.pid).create_time()
            except psutil.Error:
                ctime = time.time()
            self.popens[p["id"]] = proc
            DB.update_project(p["id"], status="running", pid=proc.pid, pid_ctime=ctime,
                              started_at=time.time(), ended_at=None, exit_code=None, desired=1,
                              container=SANDBOX.container_name(p) if SANDBOX.docker else None,
                              **({"restart_count": 0} if manual else {}))
            if envfile:
                asyncio.get_running_loop().call_later(15, lambda: envfile.unlink(missing_ok=True))
            await asyncio.sleep(1.5)
            if proc.poll() is not None:
                self.finalize(p["id"], notify=False)
                err = LOGS.last_error(p) or "\n".join(LOGS.tail_lines(p, 3))
                return False, f"Process exited immediately (code {proc.returncode}).\n{err}"
            return True, f"Started (PID {proc.pid})."

    async def stop(self, p: sqlite3.Row, force: bool = False) -> tuple[bool, str]:
        async with self.lock(p["id"]):
            p = DB.project(p["id"])  # type: ignore
            if p is None:
                return False, "Project no longer exists."
            DB.update_project(p["id"], desired=0)  # an explicit stop must survive restarts of the manager
            if not self.is_alive(p):
                if p["status"] == "running":
                    self.finalize(p["id"], notify=False)
                return False, "Project is not running."
            pid, ctime = p["pid"], p["pid_ctime"]
            if SANDBOX.docker and p["container"]:
                await run_exec([CFG.docker_bin, "kill" if force else "stop", *([] if force else ["-t", "10"]),
                                p["container"]], env=SANDBOX._client_env(), timeout=40)
            sig = signal.SIGKILL if force else signal.SIGTERM
            if pid_alive(pid, ctime) or self.is_alive(p):
                try:
                    os.killpg(pid, sig)
                except OSError:
                    pass
            deadline = time.time() + (3 if force else 12)
            while time.time() < deadline and self.is_alive(p):
                await asyncio.sleep(0.25)
            if self.is_alive(p):
                try:
                    os.killpg(pid, signal.SIGKILL)
                except OSError:
                    pass
                await asyncio.sleep(0.5)
            self.finalize(p["id"], expected=True, forced_code=-int(signal.SIGKILL if force else signal.SIGTERM))
            if SANDBOX.docker:
                await self._docker_cleanup(SANDBOX.container_name(p))
            return True, "Process killed." if force else "Process stopped."

    async def restart(self, p: sqlite3.Row, progress=None) -> tuple[bool, str]:
        if self.is_alive(DB.project(p["id"])):  # type: ignore
            await self.stop(p)
        return await self.start(p, progress)

    def write_stdin(self, p: sqlite3.Row, text: str) -> tuple[bool, str]:
        if not self.is_alive(p):
            return False, "The project is not running, so there is no stdin to write to."
        fifo = PROJECTS.fifo_path(p)
        if not fifo.exists() or not stat.S_ISFIFO(fifo.stat().st_mode):
            return False, "stdin pipe is unavailable (restart the project to create it)."
        data = (text + "\n").encode("utf-8")
        try:
            fd = os.open(fifo, os.O_WRONLY | os.O_NONBLOCK)
        except OSError as e:
            if e.errno == errno.ENXIO:
                return False, "stdin is unavailable: no process holds the input pipe open."
            return False, f"Cannot open stdin pipe: {e.strerror}"
        try:
            n = os.write(fd, data)
        except BlockingIOError:
            return False, "stdin pipe is full - the program is not reading its input."
        except OSError as e:
            return False, f"Write failed: {e.strerror}"
        finally:
            os.close(fd)
        LOGS.marker(p, f"{n} bytes written to stdin")
        return True, f"{n} bytes delivered to the process's stdin pipe."


LOGS: LogManager
PM: ProcessManager


# ============================================================================
# 8. PACKAGE MANAGER (pip inside the per-project virtualenv)
# ============================================================================
class PackageManager:
    def __init__(self) -> None:
        self.locks: dict[int, asyncio.Lock] = {}
        self.sem = asyncio.Semaphore(2)

    def lock(self, pid: int) -> asyncio.Lock:
        return self.locks.setdefault(pid, asyncio.Lock())

    async def ensure_venv(self, p: sqlite3.Row) -> tuple[bool, str]:
        if os.path.lexists(SANDBOX.venv_python_host(p)):
            return True, "ok"
        venv = SANDBOX.venv_host(p)
        shutil.rmtree(venv, ignore_errors=True)
        venv.mkdir(parents=True, exist_ok=True)
        cmd, env = SANDBOX.build_venv(p)
        rc, out = await run_exec(cmd, cwd=str(PROJECTS.src_dir(p)), env=env, timeout=300)
        if rc != 0 or not os.path.lexists(SANDBOX.venv_python_host(p)):
            shutil.rmtree(venv, ignore_errors=True)
            hint = "\n(On Debian/Ubuntu: apt install python3-venv)" if not SANDBOX.docker else ""
            return False, out[-1500:] + hint
        return True, "ok"

    async def run_pip(self, p: sqlite3.Row, args: list[str],
                      on_output: Optional[Callable[[str], Awaitable[None]]] = None) -> tuple[int, str]:
        async with self.sem, self.lock(p["id"]):
            ok, msg = await self.ensure_venv(p)
            if not ok:
                return 1, "Cannot create virtualenv:\n" + msg
            cmd, env, cname = SANDBOX.build_pip(p, args)

            async def kill_container() -> None:
                if cname:
                    await run_exec([CFG.docker_bin, "kill", cname], env=SANDBOX._client_env(), timeout=20)

            return await run_exec(cmd, cwd=str(PROJECTS.src_dir(p)), env=env, timeout=CFG.pip_timeout,
                                  on_output=on_output, on_timeout=kill_container)

    @staticmethod
    def parse_packages(text: str, expected: str, admin: bool) -> tuple[list[str], Optional[str], bool]:
        """Validate user input. Returns (packages, requirements_file, upgrade_flag)."""
        toks = [t for t in re.split(r"[\s,]+", text.strip()) if t]
        upgrade = False
        if toks and toks[0].lower() == "pip":
            toks.pop(0)
        if toks and toks[0].lower() in ("install", "uninstall"):
            sub = toks.pop(0).lower()
            if sub != expected and not (expected == "upgrade" and sub == "install"):
                raise ValueError(f"You typed 'pip {sub}' but this button is for '{expected}'. "
                                 f"Send only package names.")
        if toks and toks[0] in ("-r", "--requirement"):
            if expected == "uninstall" or len(toks) != 2:
                raise ValueError("Use exactly: -r requirements.txt")
            return [], toks[1], False
        pkgs: list[str] = []
        for t in toks:
            if t in ("-U", "--upgrade"):
                upgrade = True
                continue
            if t.startswith("-"):
                raise ValueError(f"Pip option '{t}' is not allowed. Send package names only.")
            if not PKG_RE.match(t) or len(t) > 100:
                raise ValueError(f"Invalid package spec: {t[:60]}")
            pkgs.append(t)
        if not pkgs:
            raise ValueError("No package names found.")
        if len(pkgs) > 25:
            raise ValueError("At most 25 packages per request.")
        return pkgs, None, upgrade

    @staticmethod
    def check_requirements(src: Path, rel: str, admin: bool) -> str:
        path = safe_join(src, rel)
        if not path.is_file():
            raise ValueError(f"{rel} not found in the project.")
        try:
            text = read_text_file(path, 300_000)
        except ValueError as e:
            raise ValueError(f"Cannot use {rel}: {e}")
        if not admin:
            for line in text.splitlines():
                s = line.split("#", 1)[0].strip()
                if s.startswith("-"):
                    raise ValueError(f"Option lines are not allowed in requirements for security reasons: "
                                     f"'{s[:50]}'. Remove it or ask an admin.")
        return rel_of(src, path)


PKG: PackageManager


# ============================================================================
# 9. FILE MANAGER (pure helpers; the UI is in section 12)
# ============================================================================
def list_dir(path: Path, base: Path) -> list[dict]:
    items = []
    base_r = Path(os.path.realpath(base))
    try:
        with os.scandir(path) as it:
            for e in it:
                try:
                    st = e.stat(follow_symlinks=False)
                    is_link = e.is_symlink()
                    if is_link:  # hide links that point outside of the project
                        real = Path(os.path.realpath(e.path))
                        if real != base_r and base_r not in real.parents:
                            continue
                        st = e.stat()
                    items.append({"name": e.name, "dir": stat.S_ISDIR(st.st_mode), "size": st.st_size})
                except OSError:
                    continue
    except OSError:
        return []
    items.sort(key=lambda i: (not i["dir"], i["name"].lower()))
    return items


# ============================================================================
# 10. RESOURCE MONITORING
# ============================================================================
def _tree_usage(pid: int) -> dict:
    try:
        root = psutil.Process(pid)
        procs = [root] + root.children(recursive=True)
        for pr in procs:
            try:
                pr.cpu_percent(None)
            except psutil.Error:
                pass
        time.sleep(0.3)
        cpu = rss = 0.0
        for pr in procs:
            try:
                cpu += pr.cpu_percent(None)
                rss += pr.memory_info().rss
            except psutil.Error:
                pass
        return {"cpu": f"{cpu:.1f}%", "mem": human_bytes(rss)}
    except psutil.Error:
        return {"cpu": "?", "mem": "?"}


async def project_usage(p: sqlite3.Row) -> dict:
    if SANDBOX.docker and p["container"]:
        rc, out = await run_exec([CFG.docker_bin, "stats", "--no-stream", "--format",
                                  "{{.CPUPerc}}|{{.MemUsage}}", p["container"]],
                                 env=SANDBOX._client_env(), timeout=10)
        if rc == 0 and "|" in out:
            cpu, mem = out.strip().splitlines()[-1].split("|", 1)
            return {"cpu": cpu, "mem": mem.split("/")[0].strip()}
        return {"cpu": "?", "mem": "?"}
    return await asyncio.get_running_loop().run_in_executor(None, _tree_usage, p["pid"])


async def build_status_text(user: sqlite3.Row) -> str:
    loop = asyncio.get_running_loop()
    cpu = await loop.run_in_executor(None, lambda: psutil.cpu_percent(interval=0.5))
    vm = psutil.virtual_memory()
    du = shutil.disk_usage(CFG.data_dir)
    try:
        load = os.getloadavg()
        load_s = f"{load[0]:.2f} {load[1]:.2f} {load[2]:.2f}"
    except OSError:
        load_s = "n/a"
    admin = is_admin(user["id"])
    rows = DB.all_projects() if admin else DB.projects_of(user["id"])
    projs = [PM.fresh(r["id"]) for r in rows]
    projs = [x for x in projs if x]
    running = [x for x in projs if x["status"] == "running"]
    crashed = [x for x in projs if x["status"] == "crashed"]
    stopped = len(projs) - len(running) - len(crashed)
    usage = await asyncio.gather(*[project_usage(x) for x in running[:10]]) if running else []
    uses = {x["id"]: u for x, u in zip(running[:10], usage)}
    head = (f"📊 <b>Server status</b>\n"
            f"🖥 CPU  {bar(cpu)} <b>{cpu:.0f}%</b> · {psutil.cpu_count()} cores · load {load_s}\n"
            f"🧠 RAM  {bar(vm.percent)} <b>{vm.percent:.0f}%</b> · {human_bytes(vm.used)} / {human_bytes(vm.total)}\n"
            f"💾 Disk {bar(du.used * 100 / du.total)} <b>{du.used * 100 / du.total:.0f}%</b> · {human_bytes(du.used)} / {human_bytes(du.total)}\n"
            f"🔒 Sandbox: <b>{esc(SANDBOX.mode)}</b> · manager uptime {human_dur(time.time() - START_TIME)}\n\n"
            f"{'All' if admin else 'Your'} projects: 🟢 {len(running)} running · ⚪ {stopped} stopped · 🔴 {len(crashed)} crashed\n")
    blocks = []
    for x in projs:
        lines = [f"\n{STATUS_ICON.get(x['status'], '⚪')} <b>{esc(x['name'])}</b> #{x['id']}"
                 f"{' · user ' + str(x['owner_id']) if admin else ''} — {x['status']}"]
        if x["status"] == "running":
            u = uses.get(x["id"], {})
            lines.append(f"   PID {x['pid']} · up {human_dur(PM.uptime(x) or 0)} · CPU {u.get('cpu', '-')} · RAM {u.get('mem', '-')}")
        elif x["exit_code"] is not None:
            lines.append(f"   exit code {x['exit_code']}" + (f" · ended {ts_str(x['ended_at'])}" if x["ended_at"] else ""))
        err = LOGS.last_error(x)
        if err and x["status"] != "running" or (err and x["status"] == "running"):
            lines.append(f"   ⚠️ <code>{esc(err[:110])}</code>")
        blocks.append("\n".join(lines))
    out = head
    for i, b in enumerate(blocks):
        if len(out) + len(b) > 3800:
            out += f"\n… and {len(blocks) - i} more projects"
            break
        out += b
    if not blocks:
        out += "\nNo projects yet."
    return out


# ============================================================================
# 11. TELEGRAM UI HELPERS
# ============================================================================
STATUS_ICON = {"running": "🟢", "stopped": "⚪", "crashed": "🔴", "new": "🆕"}
HandlerFn = Callable[..., Awaitable[None]]
LIVE: dict[tuple[int, int], asyncio.Task] = {}


def btn(text: str, data: str) -> InlineKeyboardButton:
    return InlineKeyboardButton(text, callback_data=data)


def kb(rows: list[list[InlineKeyboardButton]]) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(rows)


BACK_MENU = [btn("🏠 Main menu", "mm")]
MAIN_BUTTONS = [
    ("📦 Upload ZIP Project", "up"), ("📄 Upload Single .py", "us"),
    ("📂 My Projects", "pl"), ("🧩 Templates", "tp"),
    ("▶️ Start Bot", "pa:start"), ("⏹ Stop Bot", "pa:stop"),
    ("🔄 Restart Bot", "pa:restart"), ("📟 Live Logs", "pa:logs"),
    ("⌨️ Send Command", "pa:cmd"), ("📁 File Manager", "pa:files"),
    ("📦 Install Packages", "pa:pip"), ("📊 Server Status", "st"),
    ("📜 Download Logs", "pa:dlog"), ("💾 Backups", "pa:backup"),
    ("⚙️ Settings", "pa:set"), ("❓ Help", "hp"),
]


def main_menu_markup(uid: int) -> InlineKeyboardMarkup:
    rows = [[btn(*MAIN_BUTTONS[i])] + ([btn(*MAIN_BUTTONS[i + 1])] if i + 1 < len(MAIN_BUTTONS) else [])
            for i in range(0, len(MAIN_BUTTONS), 2)]
    if is_admin(uid):
        rows.append([btn("👑 Admin panel", "ad")])
    return kb(rows)


def main_menu_text(user: sqlite3.Row) -> str:
    projs = [PM.fresh(r["id"]) for r in DB.projects_of(user["id"])]
    projs = [x for x in projs if x]
    run = sum(1 for x in projs if x["status"] == "running")
    crashed = sum(1 for x in projs if x["status"] == "crashed")
    stopped = len(projs) - run - crashed
    lim = PROJECTS.user_limit(user)
    vm = psutil.virtual_memory()
    cpu = psutil.cpu_percent(interval=None)
    quota = f"{len(projs)}/{lim}  {bar(len(projs) * 100 / lim, 6)}" if lim < 10 ** 6 else f"{len(projs)}/∞"
    return (f"🚀 <b>Bot Hosting Manager</b>  <code>v{__version__}</code>\n"
            f"━━━━━━━━━━━━━━━━━━\n"
            f"👤 <b>{esc(user['username'] or 'user')}</b> · 🆔 <code>{user['id']}</code>\n"
            f"📦 Projects  <b>{quota}</b>\n"
            f"🟢 {run} running   ⚪ {stopped} stopped   🔴 {crashed} crashed\n"
            f"━━━━━━━━━━━━━━━━━━\n"
            f"🖥 CPU  {bar(cpu)} {cpu:.0f}%\n"
            f"🧠 RAM  {bar(vm.percent)} {vm.percent:.0f}%\n"
            f"🛡 Keep-alive · auto-resume after restart\n\n"
            f"Choose an action 👇")


async def reply(update: Update, text: str, markup: Optional[InlineKeyboardMarkup] = None) -> Message:
    """Edit the callback message in place, or send a new message for plain updates."""
    text = text[:4096]
    q = update.callback_query
    try:
        if q:
            m = await q.edit_message_text(text, parse_mode=HTML, reply_markup=markup,
                                          disable_web_page_preview=True)
            return m if isinstance(m, Message) else q.message  # type: ignore
        return await update.effective_message.reply_text(  # type: ignore
            text, parse_mode=HTML, reply_markup=markup, disable_web_page_preview=True)
    except BadRequest as e:
        if "not modified" in str(e).lower() and q:
            return q.message  # type: ignore
        if q:
            return await q.message.reply_text(text, parse_mode=HTML, reply_markup=markup,  # type: ignore
                                              disable_web_page_preview=True)
        raise


async def safe_edit(msg: Message, text: str, markup: Optional[InlineKeyboardMarkup] = None) -> None:
    try:
        await msg.edit_text(text[:4096], parse_mode=HTML, reply_markup=markup, disable_web_page_preview=True)
    except RetryAfter:
        pass
    except BadRequest as e:
        if "not modified" not in str(e).lower():
            log.debug("edit failed: %s", e)
    except TelegramError as e:
        log.debug("edit failed: %s", e)


def get_await(context: ContextTypes.DEFAULT_TYPE) -> Optional[dict]:
    st = context.user_data.get("await")  # type: ignore
    if st and st.get("exp", 0) < time.time():
        context.user_data.pop("await", None)  # type: ignore
        return {"kind": "_expired", "was": st.get("kind")}
    return st


def set_await(context: ContextTypes.DEFAULT_TYPE, kind: str, ttl: Optional[float] = None, **kw: Any) -> None:
    context.user_data["await"] = {"kind": kind, "exp": time.time() + (ttl or 300), **kw}  # type: ignore


def clear_await(context: ContextTypes.DEFAULT_TYPE) -> None:
    context.user_data.pop("await", None)  # type: ignore


async def guard(update: Update, context: ContextTypes.DEFAULT_TYPE) -> Optional[sqlite3.Row]:
    """Authenticate by Telegram user id. Private chats only."""
    u, chat = update.effective_user, update.effective_chat
    if not u or not chat or chat.type != "private":
        return None
    row = DB.touch_user(u.id, u.username)
    msg = None
    if row["banned"]:
        msg = "🚫 You are banned from this service."
    elif not row["approved"]:
        msg = (f"🔒 Access denied.\nThis host is private. Send your Telegram ID <code>{u.id}</code> "
               f"to the administrator to get access.")
    if msg:
        if update.callback_query:
            await update.callback_query.answer("Access denied", show_alert=True)
        elif update.effective_message:
            await update.effective_message.reply_text(msg, parse_mode=HTML)
        return None
    return row


def owned(user: sqlite3.Row, pid: Any) -> Optional[sqlite3.Row]:
    """Return the project if it belongs to the user (or user is admin)."""
    try:
        p = PM.fresh(int(pid))
    except (TypeError, ValueError):
        return None
    if p and (p["owner_id"] == user["id"] or is_admin(user["id"])):
        return p
    return None


def project_card(p: sqlite3.Row) -> str:
    st = p["status"]
    label = {"running": "🟢 Running", "stopped": "⚪ Stopped", "crashed": "🔴 Crashed", "new": "🆕 New"}.get(st, st)
    lines = [f"{STATUS_ICON.get(st, '⚪')} <b>{esc(p['name'])}</b>  <code>#{p['id']}</code>",
             "━━━━━━━━━━━━━━━━━━", f"Status: <b>{label}</b>"]
    if st == "running":
        lines.append(f"⏱ Uptime: <b>{human_dur(PM.uptime(p) or 0)}</b> · PID <code>{p['pid']}</code>")
    elif p["exit_code"] is not None:
        ran = f" · ran {human_dur(p['ended_at'] - p['started_at'])}" if p["ended_at"] and p["started_at"] else ""
        lines.append(f"Last exit code: <code>{p['exit_code']}</code>{ran}")
    args = f" {esc(p['args'])}" if p["args"] else ""
    lines.append(f"📄 <code>{esc(p['startup'] or 'no startup file')}{args}</code>")
    if SANDBOX.docker:
        lines.append(f"🐍 Python {py_version(p)} · 🔒 Docker sandbox")
    else:
        lines.append("🔒 Unsandboxed process mode")
    ka = f"ON ({p['restart_count']}/{CFG.auto_restart_max} used)" if p["auto_restart"] else "OFF"
    lines.append(f"🛡 Keep-alive: <b>{ka}</b>")
    if p["restart_every_h"]:
        lines.append(f"⏰ Scheduled restart: every {p['restart_every_h']}h")
    lines.append(f"💥 Crashes: {p['crash_count'] or 0} · ♻️ Auto-restarts: {p['total_restarts'] or 0}")
    return "\n".join(lines)


async def no_projects(update: Update) -> None:
    await reply(update, "📭 You have no projects yet.\nUpload a ZIP file containing your Python bot.",
                kb([[btn("📦 Upload ZIP Project", "up")], [btn("📄 Upload Single .py", "us")], BACK_MENU]))


# ============================================================================
# 12. TELEGRAM HANDLERS
# ============================================================================
HELP_TEXT = (
    "❓ <b>Help</b>\n\n"
    "<b>Workflow</b>: 📤 Upload ZIP → (📦 install requirements) → ▶️ Start. "
    "Each ZIP becomes its own project with its own virtualenv.\n\n"
    "<b>Logs</b>: real stdout+stderr of your process (merged), kept across restarts. "
    "Live view auto-refreshes; use ⏸ Pause / ▶️ Resume. Download gives the full TXT file.\n\n"
    "<b>Send Command</b>: text is written to the process's <i>stdin</i> (works for programs that "
    "call <code>input()</code> / read stdin). It is NOT a shell. To stop or restart use the dedicated buttons.\n\n"
    "<b>Packages</b>: pip runs inside your project's virtualenv (sandboxed). Examples: "
    "<code>requests aiohttp</code>, <code>pip install telethon</code>, <code>-r requirements.txt</code>.\n\n"
    "<b>Files</b>: browse, view, edit, upload, rename, delete, extract ZIPs inside your project. "
    "Edit-by-message is limited to 4096 chars; for larger files upload a replacement.\n\n"
    "<b>Env vars</b>: Settings → Environment variables (stored encrypted) - put tokens there, not in code.\n\n"
    "<b>New in v2</b>: 📂 project dashboards, 🧩 templates, 🔁 Update files (keeps your data, backs up, "
    "restarts automatically), 💾 backups &amp; restore, 🔍 log search, 🔑 token setter, "
    "🛡 keep-alive: crashed bots restart themselves and everything that was running resumes after a server/manager restart.\n\n"
    "Limits: ZIP ≤ {zip} MB, {mem} MB RAM and {cpu} CPU per project, {proj} projects per user. "
    "Commands: /start /menu /status /cancel /help"
)


async def cmd_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user = await guard(update, context)
    if not user:
        return
    clear_await(context)
    await update.effective_message.reply_text(  # type: ignore
        main_menu_text(user), parse_mode=HTML, reply_markup=main_menu_markup(user["id"]))


async def cmd_help(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user = await guard(update, context)
    if user:
        await update.effective_message.reply_text(  # type: ignore
            HELP_TEXT.format(zip=CFG.max_zip_mb, mem=CFG.mem_mb, cpu=CFG.cpus, proj=CFG.max_projects),
            parse_mode=HTML, reply_markup=kb([BACK_MENU]))


async def cmd_status(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user = await guard(update, context)
    if user:
        await update.effective_message.reply_text(  # type: ignore
            await build_status_text(user), parse_mode=HTML,
            reply_markup=kb([[btn("🔄 Refresh", "st")], BACK_MENU]))


async def cmd_cancel(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user = await guard(update, context)
    if user:
        clear_await(context)
        await update.effective_message.reply_text(  # type: ignore
            "❌ Cancelled.", reply_markup=main_menu_markup(user["id"]))


# ---------------------------------------------------------------- callbacks
async def on_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    q = update.callback_query
    assert q is not None
    user = await guard(update, context)
    if not user:
        return
    parts = (q.data or "").split(":")
    fn = ROUTES.get(parts[0])
    try:
        await q.answer()
    except TelegramError:
        pass
    if not fn:
        return
    await fn(update, context, user, parts[1:])


async def h_menu(update, context, user, args) -> None:
    clear_await(context)
    await reply(update, main_menu_text(user), main_menu_markup(user["id"]))


async def h_help(update, context, user, args) -> None:
    await reply(update, HELP_TEXT.format(zip=CFG.max_zip_mb, mem=CFG.mem_mb, cpu=CFG.cpus, proj=CFG.max_projects),
                kb([BACK_MENU]))


async def h_status(update, context, user, args) -> None:
    await reply(update, await build_status_text(user), kb([[btn("🔄 Refresh", "st")], BACK_MENU]))


async def h_cancel(update, context, user, args) -> None:
    clear_await(context)
    await h_menu(update, context, user, args)


# ------------------------------------------------------- project selection
async def h_pick(update, context, user, args) -> None:
    action = args[0]
    projs = DB.projects_of(user["id"])
    if not projs:
        return await no_projects(update)
    if len(projs) == 1:
        return await ACTIONS[action](update, context, user, PM.fresh(projs[0]["id"]))
    titles = {"start": "▶️ Start", "stop": "⏹ Stop", "restart": "🔄 Restart", "logs": "📟 Live logs",
              "cmd": "⌨️ Send command to", "files": "📁 Files of", "pip": "📦 Packages of",
              "dlog": "📜 Download logs of", "set": "⚙️ Settings of", "backup": "💾 Backups of",
              "update": "🔁 Update files of", "dash": "📂 Dashboard of"}
    rows = []
    for r in projs:
        p = PM.fresh(r["id"])
        rows.append([btn(f"{STATUS_ICON.get(p['status'], '⚪')} {p['name']} (#{p['id']})", f"pk:{action}:{p['id']}")])
    rows.append(BACK_MENU)
    await reply(update, f"{titles.get(action, action)} — select a project:", kb(rows))


async def h_pk(update, context, user, args) -> None:
    p = owned(user, args[1])
    if not p or args[0] not in ACTIONS:
        return await reply(update, "⚠️ Project not found.", kb([BACK_MENU]))
    await ACTIONS[args[0]](update, context, user, p)


def after_markup(p: sqlite3.Row) -> InlineKeyboardMarkup:
    return kb([[btn("📟 Logs", f"lv:{p['id']}:100:1"), btn("⌨️ Command", f"pk:cmd:{p['id']}")],
               [btn("▶️ Start", f"pk:start:{p['id']}"), btn("⏹ Stop", f"pk:stop:{p['id']}"),
                btn("🔄 Restart", f"pk:restart:{p['id']}")],
               [btn("📂 Dashboard", f"pd:{p['id']}"), btn("🏠 Main menu", "mm")]])


# --------------------------------------------------- start / stop / restart
async def act_start(update, context, user, p) -> None:
    msg = await reply(update, f"⏳ Starting <b>{esc(p['name'])}</b>…")

    async def prog(t: str) -> None:
        await safe_edit(msg, f"⏳ <b>{esc(p['name'])}</b>\n{esc(t)}")

    ok, info = await PM.start(p, prog)
    p2 = PM.fresh(p["id"])
    await safe_edit(msg, f"{'✅' if ok else '❌'} {esc(info)}\n\n{project_card(p2)}", after_markup(p2))


async def act_stop(update, context, user, p) -> None:
    msg = await reply(update, f"⏳ Stopping <b>{esc(p['name'])}</b>…")
    ok, info = await PM.stop(p)
    p2 = PM.fresh(p["id"])
    await safe_edit(msg, f"{'✅' if ok else 'ℹ️'} {esc(info)}\n\n{project_card(p2)}", after_markup(p2))


async def act_restart(update, context, user, p) -> None:
    msg = await reply(update, f"⏳ Restarting <b>{esc(p['name'])}</b>…")

    async def prog(t: str) -> None:
        await safe_edit(msg, f"⏳ <b>{esc(p['name'])}</b>\n{esc(t)}")

    await prog("Stopping…")
    ok, info = await PM.restart(p, prog)
    p2 = PM.fresh(p["id"])
    await safe_edit(msg, f"{'✅' if ok else '❌'} {esc(info)}\n\n{project_card(p2)}", after_markup(p2))


# ----------------------------------------------------------------- logs
def render_logs(p: sqlite3.Row, n: int, live: bool) -> tuple[str, InlineKeyboardMarkup]:
    lines = LOGS.tail_lines(p, n)
    body, shown = fit_tail(lines, 3200)
    running = p["status"] == "running"
    live = live and running
    state = "🔴 LIVE" if live else "⏸ Paused"
    head = (f"📟 <b>{esc(p['name'])}</b> · {STATUS_ICON.get(p['status'], '⚪')} {p['status']}"
            f"{' · exit ' + str(p['exit_code']) if p['exit_code'] is not None and not running else ''}\n"
            f"Last {shown} of {len(lines)} lines (requested {n}) · {state}\n")
    if shown < len(lines):
        head += "<i>Older lines hidden by Telegram's length limit - use Download.</i>\n"
    text = head + (f"<pre>{esc(body)}</pre>" if body else "<i>No log output yet.</i>")
    pid = p["id"]
    mode = 1 if live else 0
    rows = [[btn(("✅ " if n == x else "") + str(x), f"lv:{pid}:{x}:{mode}") for x in (50, 100, 200, 500)],
            [btn("🔄 Refresh", f"lv:{pid}:{n}:{mode}"),
             btn("⏸ Pause", f"lv:{pid}:{n}:0") if live else btn("▶️ Resume", f"lv:{pid}:{n}:1")],
            [btn("📜 Download", f"ld:{pid}"), btn("⌨️ Send input", f"pk:cmd:{pid}")],
            [btn("🔍 Search", f"ls:{pid}"), btn("🚨 Errors only", f"le:{pid}"), btn("📂 Dashboard", f"pd:{pid}")],
            [btn("▶️ Start", f"pk:start:{pid}"), btn("⏹ Stop", f"pk:stop:{pid}"), btn("🔄 Restart", f"pk:restart:{pid}")],
            BACK_MENU]
    return text, kb(rows)


def cancel_live(key: tuple[int, int]) -> None:
    t = LIVE.pop(key, None)
    if t and not t.done():
        t.cancel()


async def live_loop(bot, chat_id: int, msg_id: int, pid: int, n: int) -> None:
    key = (chat_id, msg_id)
    deadline = time.time() + CFG.live_seconds
    last = None
    try:
        while time.time() < deadline:
            await asyncio.sleep(CFG.live_interval)
            p = PM.fresh(pid)
            if not p:
                return
            running = p["status"] == "running"
            text, markup = render_logs(p, n, running)
            if (text, str(markup)) != last:
                last = (text, str(markup))
                try:
                    await bot.edit_message_text(text, chat_id=chat_id, message_id=msg_id,
                                                parse_mode=HTML, reply_markup=markup)
                except RetryAfter as e:
                    await asyncio.sleep(e.retry_after + 1)
                except BadRequest as e:
                    if "not modified" not in str(e).lower():
                        return
            if not running:
                return
        p = PM.fresh(pid)
        if p:
            text, markup = render_logs(p, n, False)
            text = text.replace("⏸ Paused", "⏸ Auto-paused (press Resume)")
            try:
                await bot.edit_message_text(text, chat_id=chat_id, message_id=msg_id,
                                            parse_mode=HTML, reply_markup=markup)
            except TelegramError:
                pass
    except asyncio.CancelledError:
        pass
    finally:
        if LIVE.get(key) is asyncio.current_task():
            LIVE.pop(key, None)


async def show_logs(update, context, p, n: int, live: bool) -> None:
    q = update.callback_query
    if q and q.message:
        cancel_live((q.message.chat_id, q.message.message_id))
    live = live and p["status"] == "running"
    text, markup = render_logs(p, n, live)
    msg = await reply(update, text, markup)
    if live:
        key = (msg.chat_id, msg.message_id)
        cancel_live(key)
        LIVE[key] = asyncio.create_task(live_loop(context.bot, msg.chat_id, msg.message_id, p["id"], n))


async def act_logs(update, context, user, p) -> None:
    await show_logs(update, context, p, 100, True)


async def h_lv(update, context, user, args) -> None:
    p = owned(user, args[0])
    if not p:
        return await reply(update, "⚠️ Project not found.", kb([BACK_MENU]))
    n = int(args[1]) if args[1].isdigit() and int(args[1]) in (50, 100, 200, 500) else 100
    await show_logs(update, context, p, n, args[2] == "1")


async def send_log_file(context, chat_id: int, p: sqlite3.Row) -> bool:
    path = LOGS.path(p)
    if not path.exists() or path.stat().st_size == 0:
        return False
    name = f"{clean_name(p['name'])}_logs.txt"
    limit = 45 * 1048576
    tmp = None
    send_path = path
    if path.stat().st_size > limit:  # Telegram bots can upload max 50 MB
        tmp = CFG.d_tmp / f"log_{p['id']}_{int(time.time())}.txt"
        with open(path, "rb") as f, open(tmp, "wb") as o:
            f.seek(-limit, 2)
            o.write(b"[... earlier output omitted: file too large for Telegram ...]\n")
            shutil.copyfileobj(f, o)
        send_path = tmp
    try:
        with open(send_path, "rb") as fh:
            await context.bot.send_document(chat_id, document=fh, filename=name,
                                            caption=f"📜 Logs of {p['name']} ({human_bytes(send_path.stat().st_size)})")
    finally:
        if tmp:
            tmp.unlink(missing_ok=True)
    return True


async def act_dlog(update, context, user, p) -> None:
    ok = await send_log_file(context, update.effective_chat.id, p)
    if not ok:
        await reply(update, f"ℹ️ <b>{esc(p['name'])}</b> has no logs yet.", kb([BACK_MENU]))


async def h_ld(update, context, user, args) -> None:
    p = owned(user, args[0])
    if p and not await send_log_file(context, update.effective_chat.id, p):
        await update.callback_query.answer("No logs yet.", show_alert=True)


# ------------------------------------------------------ Send command (stdin)
def cmd_markup(pid: int) -> InlineKeyboardMarkup:
    return kb([[btn("📟 View logs", f"lv:{pid}:50:1"), btn("🕘 History", f"ch:{pid}")],
               [btn("✅ Done", "mm"), btn("❌ Cancel", "cx")]])


async def act_cmd(update, context, user, p) -> None:
    if p["status"] != "running":
        return await reply(update, f"⚠️ <b>{esc(p['name'])}</b> is not running — there is no stdin to send to.\n"
                           f"Start it first.", kb([[btn("▶️ Start", f"pk:start:{p['id']}")], BACK_MENU]))
    set_await(context, "cmd", CFG.cmd_timeout, pid=p["id"])
    await reply(update,
                f"⌨️ <b>Console input → {esc(p['name'])}</b>\n"
                f"Send any text; each message is written to the process's <b>stdin</b> followed by a newline. "
                f"You can send several in a row. Session expires after {CFG.cmd_timeout}s of inactivity.\n\n"
                f"<i>This is not a shell: the program must read stdin (e.g. <code>input()</code>) for it to have an effect. "
                f"Use the buttons to stop/restart.</i>", cmd_markup(p["id"]))


async def send_stdin(update, context, user, p, text: str) -> None:
    ok, info = PM.write_stdin(p, text)
    if ok:
        DB.hist_add(p["id"], text)
        set_await(context, "cmd", CFG.cmd_timeout, pid=p["id"])
        await update.effective_message.reply_text(
            f"✅ Accepted: {esc(info)}\n<i>Delivery to the pipe does not guarantee the program read it - "
            f"check the logs for its response.</i>", parse_mode=HTML, reply_markup=cmd_markup(p["id"]))
    else:
        clear_await(context)
        await update.effective_message.reply_text(f"❌ Not delivered: {esc(info)}", parse_mode=HTML,
                                                  reply_markup=kb([[btn("▶️ Start", f"pk:start:{p['id']}")], BACK_MENU]))


async def h_ch(update, context, user, args) -> None:
    p = owned(user, args[0])
    if not p:
        return
    hist = DB.hist_list(p["id"], 10)
    if not hist:
        return await update.callback_query.answer("No history yet.", show_alert=True)
    rows = [[btn(("↩️ " + t.replace("\n", " "))[:45], f"hr:{hid}")] for hid, t in hist]
    rows.append([btn("⬅️ Back", f"pk:cmd:{p['id']}")])
    await reply(update, f"🕘 <b>History — {esc(p['name'])}</b>\nTap an entry to send it again.", kb(rows))


async def h_hr(update, context, user, args) -> None:
    item = DB.hist_get(int(args[0])) if args and args[0].isdigit() else None
    p = owned(user, item[0]) if item else None
    if not item or not p:
        return await reply(update, "⚠️ History entry not found.", kb([BACK_MENU]))
    await send_stdin(update, context, user, p, item[1])


# ------------------------------------------------------------ ZIP upload
async def h_up(update, context, user, args) -> None:
    set_await(context, "upload_zip", 600)
    await reply(update,
                f"📤 <b>Upload a ZIP</b>\nSend your project as a <b>file</b> (≤ {CFG.max_zip_mb} MB). "
                f"Put a name in the caption to name the project.\n"
                f"I will extract it safely, detect the startup file (app.py / main.py / bot.py …) and requirements.txt.",
                kb([[btn("❌ Cancel", "cx")]]))


async def h_us(update, context, user, args) -> None:
    """Start a new project from one Python file, while keeping ZIP upload available."""
    set_await(context, "upload_single", 600)
    await reply(update,
                "📄 <b>Upload one Python file</b>\nSend a <code>.py</code> document (not as pasted text). "
                "I’ll create a project, set that file as startup, and you can install packages or start it.\n\n"
                "For multi-file bots, use <b>📦 Upload ZIP Project</b> instead.",
                kb([[btn("❌ Cancel", "cx")]]))


async def create_project_from_single(update, context, user, doc) -> None:
    m = update.effective_message
    filename = os.path.basename((doc.file_name or "app.py").replace("\\", "/"))
    if not filename.lower().endswith(".py") or not valid_filename(filename):
        return await m.reply_text("❌ Please upload a valid .py file as a document.")
    if doc.file_size and doc.file_size > min(CFG.max_file_mb, 20) * 1048576:
        return await m.reply_text(f"❌ File too large (limit {min(CFG.max_file_mb, 20)} MB).")
    if DB.count_projects(user["id"]) >= PROJECTS.user_limit(user):
        return await m.reply_text(f"❌ Project limit reached ({PROJECTS.user_limit(user)}). Delete a project in Settings first.")
    clear_await(context)
    name = clean_name((m.caption or "").strip() or Path(filename).stem)
    p = PROJECTS.create(user["id"], PROJECTS.unique_name(user["id"], name))
    src = PROJECTS.src_dir(p)
    tmp = CFG.d_tmp / f"single_{p['id']}_{int(time.time() * 1000)}"
    try:
        tgfile = await doc.get_file()
        await tgfile.download_to_drive(str(tmp))
        if tmp.stat().st_size > CFG.max_project_mb * 1048576:
            raise ValueError(f"Project size limit ({CFG.max_project_mb} MB) exceeded.")
        target = safe_join(src, filename)
        shutil.move(str(tmp), target)
        os.chmod(target, 0o644)
        DB.update_project(p["id"], startup=filename)
        p = DB.project(p["id"])
        rows = [[btn("▶️ Start", f"pk:start:{p['id']}")],
                [btn("📦 Install packages", f"pp:{p['id']}:i"), btn("📁 Files", f"pk:files:{p['id']}")],
                [btn("⚙️ Settings", f"pk:set:{p['id']}")], BACK_MENU]
        await m.reply_text(
            f"✅ <b>Single-file project created!</b>\n<b>{esc(p['name'])}</b> (#{p['id']})\n"
            f"📄 Startup: <code>{esc(filename)}</code>\n"
            "Upload a ZIP instead if this bot needs multiple files or local modules.",
            parse_mode=HTML, reply_markup=kb(rows))
    except Exception as e:
        log.exception("single-file upload failed")
        await PROJECTS.delete(p)
        await m.reply_text(f"❌ Upload failed: {esc(e)}", parse_mode=HTML, reply_markup=kb([BACK_MENU]))
    finally:
        tmp.unlink(missing_ok=True)


async def progress_loop(msg: Message, prog: dict, stop: asyncio.Event, header: str) -> None:
    last = ""
    while not stop.is_set():
        total = max(prog.get("total", 0), 1)
        done = prog.get("done", 0)
        filled = int(10 * done / total)
        text = (f"{header}\n✅ Downloaded\n⏳ Extracting…\n"
                f"[{'█' * filled}{'░' * (10 - filled)}] {done}/{prog.get('total', 0)} entries · "
                f"{human_bytes(prog.get('bytes', 0))}")
        if text != last:
            last = text
            await safe_edit(msg, text)
        try:
            await asyncio.wait_for(stop.wait(), timeout=1.2)
        except asyncio.TimeoutError:
            pass


def startup_picker(context, p: sqlite3.Row) -> tuple[str, InlineKeyboardMarkup]:
    files = PROJECTS.list_py_files(PROJECTS.src_dir(p))
    context.user_data["sf"] = {"pid": p["id"], "files": files}
    rows = [[btn(("✅ " if f == p["startup"] else "") + f[:50], f"sf:{i}")] for i, f in enumerate(files[:30])]
    rows.append([btn("⌨️ Type a custom path", f"se:{p['id']}:sfc")])
    rows.append([btn("⬅️ Back", f"se:{p['id']}:m")])
    txt = (f"📄 <b>Startup file — {esc(p['name'])}</b>\nCurrent: <code>{esc(p['startup'] or 'not set')}</code>\n"
           f"Select the Python file to run:" if files else
           "⚠️ No .py files found in this project. Upload files via the File Manager or type a custom path.")
    return txt, kb(rows)


async def create_project_from_zip(update, context, user, doc) -> None:
    m = update.effective_message
    name_in = (m.caption or "").strip()
    if doc.file_size and doc.file_size > CFG.max_zip_mb * 1048576:
        return await m.reply_text(f"❌ ZIP is larger than {CFG.max_zip_mb} MB.")
    if DB.count_projects(user["id"]) >= PROJECTS.user_limit(user):
        return await m.reply_text(f"❌ Project limit reached ({PROJECTS.user_limit(user)}). "
                                  f"Delete a project in Settings first.")
    status = await m.reply_text("⏳ <b>Processing upload…</b>\n⏳ Downloading ZIP…", parse_mode=HTML)
    base = clean_name(name_in or Path(doc.file_name or "project").stem)
    p = PROJECTS.create(user["id"], PROJECTS.unique_name(user["id"], base))
    src = PROJECTS.src_dir(p)
    tmp = CFG.d_tmp / f"up_{p['id']}_{int(time.time())}.zip"
    clear_await(context)
    try:
        tgfile = await doc.get_file()
        await tgfile.download_to_drive(str(tmp))
        prog: dict = {"done": 0, "total": 0, "bytes": 0}
        stop = asyncio.Event()
        updater = asyncio.create_task(progress_loop(status, prog, stop, "⏳ <b>Processing upload…</b>"))
        try:
            n = await asyncio.get_running_loop().run_in_executor(None, lambda: safe_extract(tmp, src, prog))
        finally:
            stop.set()
            await updater
        startup = PROJECTS.detect_startup(src)
        if startup:
            DB.update_project(p["id"], startup=startup)
        req = PROJECTS.find_requirements(src)
        p = DB.project(p["id"])  # type: ignore
        skipped = f"\n⚠️ Skipped {prog['skipped']} symlink/special entries." if prog.get("skipped") else ""
        text = (f"✅ <b>{esc(p['name'])}</b> uploaded (#{p['id']})\n"
                f"📦 {n} files · {human_bytes(prog.get('bytes', 0))}\n"
                f"📄 Startup: <code>{esc(startup) if startup else 'not detected - please select'}</code>\n"
                f"📋 requirements.txt: {'<code>' + esc(req) + '</code> found' if req else 'not found'}{skipped}")
        rows = []
        if req:
            rows.append([btn("📦 Install requirements.txt", f"pp:{p['id']}:r")])
        if startup:
            rows.append([btn("▶️ Start", f"pk:start:{p['id']}")])
        rows.append([btn("📄 Change startup file", f"se:{p['id']}:sf"), btn("📁 Files", f"pk:files:{p['id']}")])
        rows.append(BACK_MENU)
        await safe_edit(status, text, kb(rows))
        if not startup:
            txt, mk = startup_picker(context, p)
            await m.reply_text(txt, parse_mode=HTML, reply_markup=mk)
    except ZipError as e:
        await PROJECTS.delete(p)
        await safe_edit(status, f"❌ Extraction refused: {esc(e)}", kb([BACK_MENU]))
    except Exception as e:
        log.exception("upload failed")
        await PROJECTS.delete(p)
        await safe_edit(status, f"❌ Upload failed: {esc(e)}", kb([BACK_MENU]))
    finally:
        tmp.unlink(missing_ok=True)


# ------------------------------------------------------------------- pip
def pip_menu_markup(pid: int) -> InlineKeyboardMarkup:
    return kb([[btn("➕ Install", f"pp:{pid}:i"), btn("⬆️ Upgrade", f"pp:{pid}:u")],
               [btn("➖ Uninstall", f"pp:{pid}:d"), btn("📋 List installed", f"pp:{pid}:l")],
               [btn("📄 Install requirements.txt", f"pp:{pid}:r")], BACK_MENU])


async def act_pip(update, context, user, p) -> None:
    clear_await(context)
    await reply(update,
                f"📦 <b>Packages — {esc(p['name'])}</b>\nInstalled into this project's own virtualenv "
                f"({'inside a Docker sandbox' if SANDBOX.docker else 'host process'}).\n"
                f"Pick an operation; then send package names, e.g. <code>requests aiohttp</code> or "
                f"<code>telethon==1.36.0</code>.", pip_menu_markup(p["id"]))


async def run_pip_flow(update, context, user, p, args: list[str], title: str) -> None:
    chat_id = update.effective_chat.id
    if PKG.lock(p["id"]).locked():
        await context.bot.send_message(chat_id, "⏳ Another pip operation is already running for this project; "
                                       "waiting for it to finish…")
    msg = await context.bot.send_message(chat_id, f"📦 <b>{esc(title)}</b>\n⏳ Running…", parse_mode=HTML)

    async def upd(out: str) -> None:
        body, _ = fit_tail(strip_ansi(out).splitlines(), 3000)
        await safe_edit(msg, f"📦 <b>{esc(title)}</b>\n⏳ Running…\n<pre>{esc(body)}</pre>")

    rc, out = await PKG.run_pip(p, args, upd)
    out = strip_ansi(out)
    body, shown = fit_tail(out.splitlines(), 3000)
    total_lines = len(out.splitlines())
    p2 = PM.fresh(p["id"])
    rows = [[btn("📦 Packages", f"pk:pip:{p['id']}")]]
    if p2 and p2["status"] == "running" and rc == 0:
        rows.insert(0, [btn("🔄 Restart bot to apply", f"pk:restart:{p['id']}")])
    rows.append(BACK_MENU)
    await safe_edit(msg, f"{'✅' if rc == 0 else '❌'} <b>{esc(title)}</b> — exit code {rc}\n"
                         f"<pre>{esc(body) if body else '(no output)'}</pre>", kb(rows))
    if shown < total_lines:
        tmp = CFG.d_tmp / f"pip_{p['id']}_{int(time.time())}.txt"
        tmp.write_text(out, encoding="utf-8")
        try:
            with open(tmp, "rb") as fh:
                await context.bot.send_document(chat_id, document=fh, filename="pip_output.txt",
                                                caption="Full pip output")
        finally:
            tmp.unlink(missing_ok=True)


async def h_pp(update, context, user, args) -> None:
    p = owned(user, args[0])
    if not p:
        return await reply(update, "⚠️ Project not found.", kb([BACK_MENU]))
    op = args[1]
    prompts = {"i": ("install", "➕ <b>Install packages</b>\nSend names separated by spaces/newlines.\n"
                                "Examples: <code>requests</code>, <code>aiohttp telethon aiogram</code>, "
                                "<code>pip install requests</code>, <code>-r requirements.txt</code>"),
               "u": ("upgrade", "⬆️ <b>Upgrade packages</b>\nSend the names to upgrade."),
               "d": ("uninstall", "➖ <b>Uninstall packages</b>\nSend the names to remove.")}
    if op in prompts:
        kind, text = prompts[op]
        set_await(context, f"pip_{kind}", 300, pid=p["id"])
        return await reply(update, text, kb([[btn("❌ Cancel", f"pk:pip:{p['id']}")]]))
    if op == "l":
        return await run_pip_flow(update, context, user, p, ["list"], "Installed packages")
    if op == "r":
        src = PROJECTS.src_dir(p)
        req = PROJECTS.find_requirements(src)
        if not req:
            set_await(context, "pip_reqfile", 300, pid=p["id"])
            return await reply(update, "📄 No requirements.txt in this project.\nSend one now as a <b>file</b> "
                               "(named requirements.txt) and I will install it.",
                               kb([[btn("❌ Cancel", f"pk:pip:{p['id']}")]]))
        return await install_requirements(update, context, user, p, req)


async def install_requirements(update, context, user, p, rel: str) -> None:
    try:
        rel = PKG.check_requirements(PROJECTS.src_dir(p), rel, is_admin(user["id"]))
    except ValueError as e:
        await context.bot.send_message(update.effective_chat.id, f"❌ {esc(e)}", parse_mode=HTML)
        return
    await run_pip_flow(update, context, user, p, ["install", "--progress-bar", "off", "-r", rel],
                       f"pip install -r {rel}")


async def handle_pip_text(update, context, user, st, text: str) -> None:
    p = owned(user, st["pid"])
    clear_await(context)
    if not p:
        return
    kind = st["kind"].split("_", 1)[1]
    try:
        pkgs, req, upgrade = PKG.parse_packages(text, kind, is_admin(user["id"]))
    except ValueError as e:
        set_await(context, st["kind"], 300, pid=p["id"])
        return await update.effective_message.reply_text(f"❌ {esc(e)}\nTry again or /cancel.", parse_mode=HTML)
    if req:
        return await install_requirements(update, context, user, p, req)
    if kind == "install":
        a = ["install", "--progress-bar", "off"] + (["--upgrade"] if upgrade else []) + pkgs
        title = "pip install " + " ".join(pkgs)
    elif kind == "upgrade":
        a, title = ["install", "--upgrade", "--progress-bar", "off", *pkgs], "pip install -U " + " ".join(pkgs)
    else:
        a, title = ["uninstall", "-y", *pkgs], "pip uninstall " + " ".join(pkgs)
    await run_pip_flow(update, context, user, p, a, title[:100])


# ------------------------------------------------------------- File manager
FM_PAGE = 10


def fm_session(context, user, pid: Any = None) -> Optional[dict]:
    s = context.user_data.get("fm")
    if pid is not None:
        p = owned(user, pid)
        if not p:
            return None
        s = context.user_data["fm"] = {"pid": p["id"], "rel": "", "page": 0, "names": [], "sel": None}
    return s


async def act_files(update, context, user, p) -> None:
    fm_session(context, user, p["id"])
    clear_await(context)
    await fm_show(update, context, user)


async def fm_show(update, context, user, note: str = "") -> None:
    s = context.user_data.get("fm")
    p = owned(user, s["pid"]) if s else None
    if not s or not p:
        return await reply(update, "⌛ File manager session expired. Open it again from the menu.", kb([BACK_MENU]))
    src = PROJECTS.src_dir(p)
    try:
        cur = safe_join(src, s["rel"])
        if not cur.is_dir():
            raise ValueError
    except ValueError:
        s["rel"] = ""
        cur = safe_join(src, "")
    items = list_dir(cur, src)
    s["names"] = [i["name"] for i in items]
    pages = max(1, (len(items) + FM_PAGE - 1) // FM_PAGE)
    s["page"] = min(max(0, s["page"]), pages - 1)
    chunk = items[s["page"] * FM_PAGE:(s["page"] + 1) * FM_PAGE]
    rows = []
    for off, it in enumerate(chunk):
        idx = s["page"] * FM_PAGE + off
        label = f"📁 {it['name']}/" if it["dir"] else f"📄 {it['name']} · {human_bytes(it['size'])}"
        rows.append([btn(label[:60], f"fm:o:{idx}")])
    if pages > 1:
        rows.append([btn("◀️", f"fm:pg:{s['page'] - 1}"), btn(f"{s['page'] + 1}/{pages}", "fm:r"),
                     btn("▶️", f"fm:pg:{s['page'] + 1}")])
    rows.append([btn("⬆️ Up", "fm:up"), btn("📤 Upload", "fm:ul"), btn("📁 New folder", "fm:mk"), btn("📝 New file", "fm:nf")])
    rows.append([btn("🔄 Refresh", "fm:r"), btn("🏠 Main menu", "mm")])
    used = await asyncio.get_running_loop().run_in_executor(None, dir_size, src)
    text = (f"{note}📁 <b>{esc(p['name'])}</b>\n<code>/{esc(s['rel'])}</code>\n"
            f"{sum(1 for i in items if i['dir'])} folders · {sum(1 for i in items if not i['dir'])} files · "
            f"project size {human_bytes(used)}" + ("" if items else "\n<i>Empty folder</i>"))
    await reply(update, text, kb(rows))


def fm_file_markup(name: str, is_zip: bool) -> InlineKeyboardMarkup:
    rows = [[btn("⬇️ Download", "fa:dl"), btn("👁 View", "fa:vw:0")],
            [btn("✏️ Edit (overwrite)", "fa:ed"), btn("🔎 Find & replace", "fa:fr")],
            [btn("🏷 Rename", "fa:rn"), btn("🗑 Delete", "fa:rm")]]
    if is_zip:
        rows.append([btn("🗜 Extract here (safe)", "fa:ex")])
    rows.append([btn("⬅️ Back to folder", "fm:r")])
    return kb(rows)


def fm_sel_path(context, user) -> tuple[Optional[sqlite3.Row], Optional[Path], Optional[dict]]:
    s = context.user_data.get("fm")
    p = owned(user, s["pid"]) if s else None
    if not s or not p or not s.get("sel"):
        return None, None, None
    try:
        path = safe_join(PROJECTS.src_dir(p), (s["rel"] + "/" + s["sel"]) if s["rel"] else s["sel"])
    except ValueError:
        return p, None, s
    return p, path, s


async def h_fm(update, context, user, args) -> None:
    s = context.user_data.get("fm")
    p = owned(user, s["pid"]) if s else None
    if not s or not p:
        return await reply(update, "⌛ File manager session expired. Open it again from the menu.", kb([BACK_MENU]))
    op = args[0]
    clear_await(context)
    src = PROJECTS.src_dir(p)
    if op == "o":
        try:
            name = s["names"][int(args[1])]
        except (IndexError, ValueError):
            return await fm_show(update, context, user, "⚠️ Listing changed - refreshed.\n")
        path = safe_join(src, (s["rel"] + "/" + name) if s["rel"] else name)
        if path.is_dir():
            s["rel"], s["page"] = rel_of(src, path), 0
            return await fm_show(update, context, user)
        s["sel"] = name
        size = path.stat().st_size if path.exists() else 0
        return await reply(update, f"📄 <b>{esc(name)}</b>\n<code>/{esc(rel_of(src, path))}</code> · {human_bytes(size)}",
                           fm_file_markup(name, name.lower().endswith(".zip")))
    if op == "up":
        if s["rel"]:
            s["rel"] = "/".join(s["rel"].split("/")[:-1])
            s["page"] = 0
    elif op == "pg":
        s["page"] = int(args[1])
    elif op == "ul":
        set_await(context, "fm_upload", 600)
        return await reply(update, f"📤 <b>Upload to</b> <code>/{esc(s['rel'])}</code>\nSend one or more files as "
                           f"documents (≤ {CFG.max_file_mb} MB each). ZIPs are stored as-is; use Extract afterwards.",
                           kb([[btn("✅ Done", "fm:r")]]))
    elif op == "mk":
        set_await(context, "fm_mkdir", 300)
        return await reply(update, "📁 Send the new folder name:", kb([[btn("❌ Cancel", "fm:r")]]))
    elif op == "nf":
        set_await(context, "fm_newfile", 300)
        return await reply(update, "📝 Send the file name on the <b>first line</b>; the content (optional) follows on the "
                           "next lines.", kb([[btn("❌ Cancel", "fm:r")]]))
    await fm_show(update, context, user)


async def h_fa(update, context, user, args) -> None:
    p, path, s = fm_sel_path(context, user)
    if not p or not s:
        return await reply(update, "⌛ Session expired. Open the File Manager again.", kb([BACK_MENU]))
    if path is None:
        return await reply(update, "⛔ Path rejected (outside the project).", kb([BACK_MENU]))
    op = args[0]
    name = s["sel"]
    chat_id = update.effective_chat.id
    if not path.exists():
        return await fm_show(update, context, user, "⚠️ That file no longer exists.\n")
    if op == "dl":
        if not path.is_file():
            return
        if path.stat().st_size > 45 * 1048576:
            return await update.callback_query.answer("File too large for Telegram (45 MB max).", show_alert=True)
        with open(path, "rb") as fh:
            await context.bot.send_document(chat_id, document=fh, filename=name)
    elif op == "vw":
        page = int(args[1]) if len(args) > 1 and args[1].isdigit() else 0
        try:
            text = read_text_file(path, 500_000)
        except ValueError as e:
            return await update.callback_query.answer(f"Cannot display: {e}. Use Download.", show_alert=True)
        size = 3000
        pages = max(1, (len(text) + size - 1) // size)
        page = min(page, pages - 1)
        nav = []
        if page > 0:
            nav.append(btn("◀️", f"fa:vw:{page - 1}"))
        nav.append(btn(f"{page + 1}/{pages}", f"fa:vw:{page}"))
        if page < pages - 1:
            nav.append(btn("▶️", f"fa:vw:{page + 1}"))
        await reply(update, f"👁 <b>{esc(name)}</b>\n<pre>{esc(text[page * size:(page + 1) * size]) or '(empty)'}</pre>",
                    kb([nav, [btn("✏️ Edit", "fa:ed"), btn("⬅️ Back", f"fm:o:{s['names'].index(name)}")]]))
    elif op == "ed":
        set_await(context, "fm_edit", 600)
        await reply(update, f"✏️ <b>Edit {esc(name)}</b>\nSend the <b>new full content</b> as a message "
                    f"(≤ 4096 chars) — or upload a file to replace it.", kb([[btn("❌ Cancel", "fm:r")]]))
    elif op == "fr":
        set_await(context, "fm_replace", 300)
        await reply(update, f"🔎 <b>Find & replace in {esc(name)}</b>\nSend: <code>old text ||| new text</code> "
                    f"(replaces all occurrences).", kb([[btn("❌ Cancel", "fm:r")]]))
    elif op == "rn":
        set_await(context, "fm_rename", 300)
        await reply(update, f"🏷 Send the new name for <b>{esc(name)}</b>:", kb([[btn("❌ Cancel", "fm:r")]]))
    elif op == "rm":
        await reply(update, f"🗑 Delete <b>{esc(name)}</b>{' and everything inside it' if path.is_dir() else ''}? "
                    f"This cannot be undone.", kb([[btn("✅ Yes, delete", "fa:rmy"), btn("❌ No", "fm:r")]]))
    elif op == "rmy":
        try:
            shutil.rmtree(path) if path.is_dir() and not path.is_symlink() else path.unlink()
            s["sel"] = None
            await fm_show(update, context, user, f"🗑 Deleted <code>{esc(name)}</code>\n")
        except OSError as e:
            await reply(update, f"❌ Delete failed: {esc(e.strerror)}", kb([BACK_MENU]))
    elif op == "ex":
        if not path.is_file():
            return
        stem = clean_name(Path(name).stem, "extracted")
        dest = path.parent / stem
        i = 2
        while dest.exists():
            dest = path.parent / f"{stem}-{i}"
            i += 1
        msg = await reply(update, f"🗜 Extracting <b>{esc(name)}</b>…")
        prog: dict = {"done": 0, "total": 0, "bytes": 0}
        stop = asyncio.Event()
        upd = asyncio.create_task(progress_loop(msg, prog, stop, f"🗜 <b>{esc(name)}</b>"))
        try:
            n = await asyncio.get_running_loop().run_in_executor(
                None, lambda: safe_extract(path, dest, prog, strip_top=False))
            stop.set(); await upd
            await fm_show(update, context, user, f"✅ Extracted {n} files to <code>{esc(dest.name)}/</code>\n")
        except ZipError as e:
            stop.set(); await upd
            shutil.rmtree(dest, ignore_errors=True)
            await safe_edit(msg, f"❌ Extraction refused: {esc(e)}", kb([[btn("⬅️ Back", "fm:r")]]))


async def fm_text_input(update, context, user, st, text: str) -> None:
    kind = st["kind"]
    s = context.user_data.get("fm")
    p = owned(user, s["pid"]) if s else None
    if not s or not p:
        clear_await(context)
        return await update.effective_message.reply_text("⌛ Session expired. Open the File Manager again.")
    src = PROJECTS.src_dir(p)
    back = fm_back_markup(p)
    clear_await(context)
    m = update.effective_message
    try:
        cwd = safe_join(src, s["rel"])
        if kind == "fm_mkdir":
            name = text.strip()
            if not valid_filename(name):
                raise ValueError("Invalid folder name")
            (cwd / name).mkdir(exist_ok=False)
            return await m.reply_text(f"✅ Folder <code>{esc(name)}</code> created.", parse_mode=HTML, reply_markup=back)
        if kind == "fm_newfile":
            first, _, body = text.partition("\n")
            name = first.strip()
            if not valid_filename(name):
                raise ValueError("Invalid file name")
            target = cwd / name
            if target.exists():
                raise ValueError("A file with that name already exists")
            atomic_write(target, body.encode())
            return await m.reply_text(f"✅ File <code>{esc(name)}</code> created.", parse_mode=HTML, reply_markup=back)
        p2, path, _ = fm_sel_path(context, user)
        if not path or not path.exists():
            raise ValueError("Selected file not found")
        if kind == "fm_rename":
            new = text.strip()
            if not valid_filename(new):
                raise ValueError("Invalid name")
            dest = path.parent / new
            if dest.exists():
                raise ValueError("Target name already exists")
            safe_join(src, rel_of(src, dest))
            path.rename(dest)
            s["sel"] = new
            return await m.reply_text(f"✅ Renamed to <code>{esc(new)}</code>.", parse_mode=HTML, reply_markup=back)
        if not path.is_file():
            raise ValueError("Not a regular file")
        if kind == "fm_edit":
            atomic_write(path, text.encode("utf-8"))
            return await m.reply_text(f"✅ <code>{esc(path.name)}</code> overwritten ({len(text)} chars).",
                                      parse_mode=HTML, reply_markup=back)
        if kind == "fm_replace":
            if "|||" not in text:
                raise ValueError("Use the format: old ||| new")
            old, new = (x.strip("\n") for x in text.split("|||", 1))
            old = old.strip() if old.strip() == old.strip(" ") else old
            if not old:
                raise ValueError("The text to find is empty")
            content = read_text_file(path)
            cnt = content.count(old)
            if cnt == 0:
                raise ValueError("Text not found in the file")
            atomic_write(path, content.replace(old, new.lstrip(" ") if new.startswith(" ") else new).encode())
            return await m.reply_text(f"✅ Replaced {cnt} occurrence(s) in <code>{esc(path.name)}</code>.",
                                      parse_mode=HTML, reply_markup=back)
    except FileExistsError:
        await m.reply_text("❌ Already exists.", reply_markup=back)
    except (ValueError, OSError) as e:
        await m.reply_text(f"❌ {esc(getattr(e, 'strerror', None) or e)}", parse_mode=HTML, reply_markup=back)


async def fm_receive_document(update, context, user, st, doc) -> None:
    """Document arrived while in file-manager upload/edit mode."""
    s = context.user_data.get("fm")
    p = owned(user, s["pid"]) if s else None
    m = update.effective_message
    if not s or not p:
        return await m.reply_text("⌛ Session expired. Open the File Manager again.")
    if doc.file_size and doc.file_size > min(CFG.max_file_mb, 20) * 1048576:
        return await m.reply_text(f"❌ File too large (limit {min(CFG.max_file_mb, 20)} MB for Telegram uploads).")
    src = PROJECTS.src_dir(p)
    used = await asyncio.get_running_loop().run_in_executor(None, dir_size, src)
    if used + (doc.file_size or 0) > CFG.max_project_mb * 1048576:
        return await m.reply_text(f"❌ Project size limit ({CFG.max_project_mb} MB) would be exceeded.")
    tmp = CFG.d_tmp / f"fm_{p['id']}_{int(time.time() * 1000)}"
    try:
        f = await doc.get_file()
        await f.download_to_drive(str(tmp))
        if st["kind"] == "fm_edit":
            _, path, _ = fm_sel_path(context, user)
            if not path or not path.is_file():
                raise ValueError("Selected file not found")
            shutil.move(str(tmp), path)
            clear_await(context)
            return await m.reply_text(f"✅ <code>{esc(path.name)}</code> replaced.", parse_mode=HTML,
                                      reply_markup=fm_back_markup(p))
        name = os.path.basename((doc.file_name or "upload").replace("\\", "/"))
        if not valid_filename(name):
            raise ValueError("Invalid file name")
        cwd = safe_join(src, s["rel"])
        shutil.move(str(tmp), cwd / name)
        os.chmod(cwd / name, 0o644)
        set_await(context, "fm_upload", 600)
        await m.reply_text(f"✅ Saved <code>{esc(name)}</code> ({human_bytes(doc.file_size or 0)}). Send more or press Done.",
                           parse_mode=HTML, reply_markup=kb([[btn("✅ Done", "fm:r")]]))
    except (ValueError, OSError) as e:
        await m.reply_text(f"❌ {esc(getattr(e, 'strerror', None) or e)}", parse_mode=HTML)
    finally:
        tmp.unlink(missing_ok=True)


async def pip_reqfile_received(update, context, user, st, doc) -> None:
    p = owned(user, st["pid"])
    m = update.effective_message
    if not p:
        return
    if (doc.file_size or 0) > 300_000:
        return await m.reply_text("❌ requirements file too large (300 KB max).")
    clear_await(context)
    tmp = CFG.d_tmp / f"req_{p['id']}_{int(time.time())}"
    try:
        f = await doc.get_file()
        await f.download_to_drive(str(tmp))
        shutil.move(str(tmp), PROJECTS.src_dir(p) / "requirements.txt")
    finally:
        tmp.unlink(missing_ok=True)
    await install_requirements(update, context, user, p, "requirements.txt")


# -------------------------------------------------------------- Settings
def settings_markup(p: sqlite3.Row) -> InlineKeyboardMarkup:
    pid = p["id"]
    sch = p["restart_every_h"]
    rows = [[btn("📄 Startup file", f"se:{pid}:sf"), btn("🧾 Arguments", f"se:{pid}:args")],
            [btn("🔑 Bot token", f"se:{pid}:tk"), btn("🔐 Environment vars", f"ev:{pid}:m")],
            [btn(f"🛡 Keep-alive: {'ON' if p['auto_restart'] else 'OFF'}", f"se:{pid}:ar"),
             btn(f"⏰ Schedule: {'every ' + str(sch) + 'h' if sch else 'off'}", f"se:{pid}:sch")]]
    row = [btn("🧹 Clear logs", f"se:{pid}:cl")]
    if SANDBOX.docker:
        row.insert(0, btn(f"🐍 Python {py_version(p)}", f"se:{pid}:py"))
    rows += [row, [btn("🏷 Rename", f"se:{pid}:rn"), btn("☠️ Force kill", f"se:{pid}:kl")],
             [btn("🗑 Delete project", f"se:{pid}:dl")],
             [btn("📂 Dashboard", f"pd:{pid}"), btn("🏠 Main menu", "mm")]]
    return kb(rows)


async def act_set(update, context, user, p) -> None:
    clear_await(context)
    lim = PROJECTS.user_limit(user)
    await reply(update, f"⚙️ <b>Settings</b>\n{project_card(p)}\n\nYour project limit: "
                f"{lim if lim < 10 ** 6 else '∞'} · RAM {CFG.mem_mb} MB · CPU {CFG.cpus}", settings_markup(p))


async def h_se(update, context, user, args) -> None:
    p = owned(user, args[0])
    if not p:
        return await reply(update, "⚠️ Project not found.", kb([BACK_MENU]))
    op = args[1]
    pid = p["id"]
    if op == "m":
        return await act_set(update, context, user, p)
    if op == "sf":
        txt, mk = startup_picker(context, p)
        return await reply(update, txt, mk)
    if op == "sfc":
        set_await(context, "startup_custom", 300, pid=pid)
        return await reply(update, "⌨️ Send the startup file path relative to the project root "
                           "(e.g. <code>src/main.py</code>):", kb([[btn("❌ Cancel", f"se:{pid}:m")]]))
    if op == "ar":
        DB.update_project(pid, auto_restart=0 if p["auto_restart"] else 1, restart_count=0)
        return await act_set(update, context, user, PM.fresh(pid))
    if op == "tk":
        has = "BOT_TOKEN" in DB.env_get(pid)
        set_await(context, "token_set", 300, pid=pid)
        return await reply(update, f"🔑 <b>Bot token — {esc(p['name'])}</b>\nCurrently: {'✅ set' if has else '❌ not set'}\n\n"
                           "Send the token from @BotFather. It is verified with Telegram, stored <b>encrypted</b> as "
                           "<code>BOT_TOKEN</code>, and your message is deleted immediately. A running bot is restarted "
                           "to use it.", kb([[btn("❌ Cancel", f"pd:{pid}")]]))
    if op == "args":
        set_await(context, "args_set", 300, pid=pid)
        return await reply(update, f"🧾 <b>Startup arguments</b>\nCurrent: <code>{esc(p['args'] or 'none')}</code>\n"
                           "Send them as you would type after the script name, e.g. <code>--debug --port 8080</code>. "
                           "Send <code>-</code> to clear.", kb([[btn("❌ Cancel", f"se:{pid}:m")]]))
    if op == "sch":
        rows = [[btn(("✅ " if (p["restart_every_h"] or 0) == h else "") + (f"Every {h}h" if h else "Off"),
                     f"se:{pid}:sc:{h}") for h in SCHEDULE_CHOICES], [btn("⬅️ Back", f"se:{pid}:m")]]
        return await reply(update, "⏰ <b>Scheduled restart</b>\nRestart this project automatically after it has been "
                           "running for the chosen time (fresh memory, reconnects).", kb(rows))
    if op == "sc":
        h = int(args[2]) if len(args) > 2 and args[2].isdigit() else 0
        if h in SCHEDULE_CHOICES:
            DB.update_project(pid, restart_every_h=h)
        return await act_set(update, context, user, PM.fresh(pid))
    if op == "py":
        if not SANDBOX.docker:
            return await update.callback_query.answer("Python versions need Docker mode.", show_alert=True)
        rows = [[btn(("✅ " if py_version(p) == v else "") + f"Python {v}", f"se:{pid}:pv:{v}")] for v in CFG.python_versions]
        rows.append([btn("⬅️ Back", f"se:{pid}:m")])
        return await reply(update, "🐍 <b>Python version</b>\nThe project's virtualenv is rebuilt for the new version; "
                           "reinstall packages afterwards. Your files and data are untouched.", kb(rows))
    if op == "pv":
        ver = args[2] if len(args) > 2 else ""
        if ver not in CFG.python_versions:
            return await update.callback_query.answer("Unknown version.", show_alert=True)
        if p["status"] == "running":
            return await update.callback_query.answer("Stop the project first.", show_alert=True)
        DB.update_project(pid, image=f"python:{ver}-slim")
        await asyncio.get_running_loop().run_in_executor(
            None, lambda: shutil.rmtree(SANDBOX.venv_host(p), ignore_errors=True))
        rows = []
        if PROJECTS.find_requirements(PROJECTS.src_dir(p)):
            rows.append([btn("📦 Install requirements.txt", f"pp:{pid}:r")])
        rows.append([btn("⚙️ Settings", f"se:{pid}:m")])
        return await reply(update, f"✅ Python set to <b>{ver}</b>. The virtualenv will be rebuilt on next use.", kb(rows))
    if op == "cl":
        try:
            with open(LOGS.path(p), "r+b") as f:
                f.truncate(0)
        except OSError:
            pass
        await update.callback_query.answer("Logs cleared.")
        return await act_set(update, context, user, PM.fresh(pid))
    if op == "rn":
        set_await(context, "proj_rename", 300, pid=pid)
        return await reply(update, "🏷 Send the new project name:", kb([[btn("❌ Cancel", f"se:{pid}:m")]]))
    if op == "kl":
        ok, info = await PM.stop(p, force=True)
        await update.callback_query.answer(info, show_alert=True)
        return await act_set(update, context, user, PM.fresh(pid))
    if op == "dl":
        return await reply(update, f"🗑 <b>Delete project {esc(p['name'])}?</b>\nThe process is stopped, files, venv "
                           f"and logs are removed (a backup ZIP is kept on the server).",
                           kb([[btn("✅ Yes, delete", f"se:{pid}:dly"), btn("❌ No", f"se:{pid}:m")]]))
    if op == "dly":
        await PROJECTS.delete(p)
        return await reply(update, f"🗑 Project <b>{esc(p['name'])}</b> deleted.", kb([BACK_MENU]))


async def h_sf(update, context, user, args) -> None:
    s = context.user_data.get("sf")
    p = owned(user, s["pid"]) if s else None
    if not s or not p:
        return await reply(update, "⌛ Session expired.", kb([BACK_MENU]))
    try:
        rel = s["files"][int(args[0])]
        safe_join(PROJECTS.src_dir(p), rel)
    except (IndexError, ValueError):
        return await reply(update, "⚠️ Invalid selection.", kb([BACK_MENU]))
    DB.update_project(p["id"], startup=rel)
    p = PM.fresh(p["id"])
    await reply(update, f"✅ Startup file set to <code>{esc(rel)}</code>\n\n{project_card(p)}", after_markup(p))


# ----------------------------------------------------- Environment variables
async def h_ev(update, context, user, args) -> None:
    p = owned(user, args[0])
    if not p:
        return await reply(update, "⚠️ Project not found.", kb([BACK_MENU]))
    op = args[1]
    if op == "add":
        set_await(context, "env_add", 300, pid=p["id"])
        return await reply(update, "➕ Send one or more lines <code>KEY=VALUE</code>.\nYour message is deleted "
                           "right after saving so secrets don't stay in the chat.",
                           kb([[btn("❌ Cancel", f"ev:{p['id']}:m")]]))
    if op == "rm" and len(args) > 2:
        DB.env_del(p["id"], args[2])
    env = DB.env_get(p["id"])
    rows = [[btn(f"🗑 {k}", f"ev:{p['id']}:rm:{k}")] for k in env]
    rows.append([btn("➕ Add variable", f"ev:{p['id']}:add")])
    rows.append([btn("⬅️ Back", f"se:{p['id']}:m")])
    listing = "\n".join(f"• <code>{esc(k)}</code> = ••••••" for k in env) or "<i>none</i>"
    await reply(update, f"🔐 <b>Environment variables — {esc(p['name'])}</b>\n{listing}\n\n"
                f"Values are encrypted at rest and applied on the next (re)start. Tap to delete.", kb(rows))


async def handle_env_add(update, context, user, st, text: str) -> None:
    p = owned(user, st["pid"])
    clear_await(context)
    if not p:
        return
    saved, errors = [], []
    for line in text.splitlines():
        if not line.strip():
            continue
        k, sep, v = line.partition("=")
        k = k.strip()
        if not sep or not ENV_KEY_RE.match(k) or k.upper() in BLOCKED_ENV or k.upper().startswith("LD_"):
            errors.append(k[:30] or "?")
            continue
        DB.env_set(p["id"], k, v.strip().strip('"').strip("'"))
        saved.append(k)
    try:
        await update.effective_message.delete()
    except TelegramError:
        pass
    note = f"✅ Saved: {', '.join(esc(k) for k in saved)}" if saved else "ℹ️ Nothing saved."
    if errors:
        note += f"\n❌ Rejected (bad/blocked name or format): {', '.join(esc(e) for e in errors)}"
    await context.bot.send_message(update.effective_chat.id, note, parse_mode=HTML,
                                   reply_markup=kb([[btn("🔐 Variables", f"ev:{p['id']}:m")], BACK_MENU]))


# ----------------------------------------------------- text / document routers
async def on_text(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user = await guard(update, context)
    if not user:
        return
    m = update.effective_message
    text = m.text or ""  # type: ignore
    st = get_await(context)
    if not st:
        return await m.reply_text("Use the menu below 👇", reply_markup=main_menu_markup(user["id"]))  # type: ignore
    kind = st["kind"]
    if kind == "_expired":
        return await m.reply_text(  # type: ignore
            "⌛ That session timed out. Start again from the menu.", reply_markup=main_menu_markup(user["id"]))
    if kind == "cmd":
        p = owned(user, st["pid"])
        if not p:
            clear_await(context)
            return
        if len(text) > 1000:
            return await m.reply_text("❌ Input too long (max 1000 characters).")  # type: ignore
        return await send_stdin(update, context, user, p, text)
    if kind.startswith("pip_") and kind != "pip_reqfile":
        return await handle_pip_text(update, context, user, st, text)
    if kind.startswith("fm_") and kind not in ("fm_upload",):
        return await fm_text_input(update, context, user, st, text)
    if kind == "env_add":
        return await handle_env_add(update, context, user, st, text)
    if kind == "token_set":
        return await handle_token_set(update, context, user, st, text)
    if kind == "args_set":
        return await handle_args_set(update, context, user, st, text)
    if kind == "log_search":
        return await handle_log_search(update, context, user, st, text)
    if kind in ("startup_custom", "proj_rename"):
        p = owned(user, st["pid"])
        clear_await(context)
        if not p:
            return
        if kind == "proj_rename":
            new = PROJECTS.unique_name(p["owner_id"], clean_name(text, p["name"]))
            DB.update_project(p["id"], name=new)
            return await m.reply_text(f"✅ Renamed to <b>{esc(new)}</b>.", parse_mode=HTML,  # type: ignore
                                      reply_markup=kb([[btn("⚙️ Settings", f"pk:set:{p['id']}")], BACK_MENU]))
        rel = text.strip().replace("\\", "/").lstrip("/")
        try:
            path = safe_join(PROJECTS.src_dir(p), rel)
            if not path.is_file() or not rel.endswith(".py"):
                raise ValueError("File not found or not a .py file")
        except ValueError as e:
            return await m.reply_text(f"❌ {esc(e)}", parse_mode=HTML)  # type: ignore
        rel = rel_of(PROJECTS.src_dir(p), path)
        DB.update_project(p["id"], startup=rel)
        return await m.reply_text(f"✅ Startup file set to <code>{esc(rel)}</code>", parse_mode=HTML,  # type: ignore
                                  reply_markup=after_markup(PM.fresh(p["id"])))
    await m.reply_text("Please send a file for this step, or /cancel.")  # type: ignore


async def on_document(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user = await guard(update, context)
    if not user:
        return
    m = update.effective_message
    doc = m.document  # type: ignore
    st = get_await(context)
    fname = (doc.file_name or "").lower()
    if st and st["kind"] in ("fm_upload", "fm_edit"):
        return await fm_receive_document(update, context, user, st, doc)
    if st and st["kind"] == "pip_reqfile":
        return await pip_reqfile_received(update, context, user, st, doc)
    if st and st["kind"] == "update_files":
        return await update_project_files(update, context, user, st, doc)
    if st and st["kind"] == "upload_single":
        return await create_project_from_single(update, context, user, doc)
    if st and st["kind"] == "upload_zip":
        if not fname.endswith(".zip"):
            return await m.reply_text("❌ Please send a .zip file, or choose Upload Single .py.")
        return await create_project_from_zip(update, context, user, doc)
    if fname.endswith(".zip"):
        return await create_project_from_zip(update, context, user, doc)
    await m.reply_text("ℹ️ To add a single file use 📁 File Manager → 📤 Upload. "
                       "To create a project send a .zip.")  # type: ignore


# ============================================================================
# 12b. EXTRA FEATURES (v2): dashboard, templates, update, backups, token, search
# ============================================================================
SCHEDULE_CHOICES = (0, 6, 12, 24)
DATA_SUFFIXES = (".db", ".sqlite", ".sqlite3", ".session", ".session-journal", ".pickle", ".pkl",
                 ".dat", ".shelve", ".json")
DATA_DIR_NAMES = {"data", "database", "db", "storage", "sessions", "session", "uploads", "downloads"}
TOKEN_RE = re.compile(r"^\d{5,}:[A-Za-z0-9_-]{30,}$")


def keep_data(parts: list) -> bool:
    """True for files that hold the user's data and must survive an update."""
    return parts[-1].lower().endswith(DATA_SUFFIXES) or any(x.lower() in DATA_DIR_NAMES for x in parts[:-1])


def fm_back_markup(p: sqlite3.Row) -> InlineKeyboardMarkup:
    rows = [[btn("📁 Back to files", "fm:r")]]
    if p["status"] == "running":
        rows.insert(0, [btn("🔄 Restart to apply changes", f"pk:restart:{p['id']}")])
    return kb(rows)


# ------------------------------------------------------------- dashboard
def projects_view(user: sqlite3.Row) -> tuple[str, InlineKeyboardMarkup]:
    projs = [PM.fresh(r["id"]) for r in DB.projects_of(user["id"])]
    projs = [x for x in projs if x]
    if not projs:
        return ("📭 You have no projects yet.\nUpload a ZIP / .py file or start from a 🧩 template.",
                kb([[btn("📦 Upload ZIP Project", "up"), btn("📄 Upload Single .py", "us")],
                    [btn("🧩 Templates", "tp")], BACK_MENU]))
    run = sum(1 for x in projs if x["status"] == "running")
    crashed = sum(1 for x in projs if x["status"] == "crashed")
    rows = []
    for x in projs:
        extra = f" · {human_dur(PM.uptime(x) or 0)}" if x["status"] == "running" else ""
        rows.append([btn(f"{STATUS_ICON.get(x['status'], '⚪')} {x['name']}{extra}", f"pd:{x['id']}")])
    rows.append([btn("📦 Upload ZIP", "up"), btn("🧩 Templates", "tp")])
    rows.append(BACK_MENU)
    return (f"📂 <b>My Projects</b>\n━━━━━━━━━━━━━━━━━━\n🟢 {run} running · ⚪ {len(projs) - run - crashed} stopped "
            f"· 🔴 {crashed} crashed\nTap a project to open its dashboard:", kb(rows))


async def h_projects(update, context, user, args) -> None:
    clear_await(context)
    text, markup = projects_view(user)
    await reply(update, text, markup)


def dash_markup(p: sqlite3.Row) -> InlineKeyboardMarkup:
    pid = p["id"]
    first = ([btn("⏹ Stop", f"pk:stop:{pid}"), btn("🔄 Restart", f"pk:restart:{pid}")]
             if p["status"] == "running" else [btn("▶️ Start", f"pk:start:{pid}")])
    return kb([first,
               [btn("📟 Live logs", f"lv:{pid}:100:1"), btn("⌨️ Console", f"pk:cmd:{pid}")],
               [btn("🔍 Search logs", f"ls:{pid}"), btn("🚨 Errors", f"le:{pid}")],
               [btn("📁 Files", f"pk:files:{pid}"), btn("📦 Packages", f"pk:pip:{pid}")],
               [btn("🔁 Update files", f"pk:update:{pid}"), btn("💾 Backups", f"pk:backup:{pid}")],
               [btn("🔑 Bot token", f"se:{pid}:tk"), btn("⚙️ Settings", f"pk:set:{pid}")],
               [btn("📂 My projects", "pl"), btn("🏠 Menu", "mm")]])


async def act_dash(update, context, user, p) -> None:
    clear_await(context)
    text = project_card(p)
    if p["status"] == "running":
        u = await project_usage(p)
        text += f"\n📈 CPU <b>{esc(u['cpu'])}</b> · RAM <b>{esc(u['mem'])}</b> (limit {CFG.mem_mb} MB)"
    err = LOGS.last_error(p)
    if err:
        text += f"\n⚠️ Last error: <code>{esc(err[:120])}</code>"
    await reply(update, text, dash_markup(p))


async def h_pd(update, context, user, args) -> None:
    p = owned(user, args[0] if args else None)
    if not p:
        return await reply(update, "⚠️ Project not found.", kb([BACK_MENU]))
    await act_dash(update, context, user, p)


# ------------------------------------------------------------- templates
TPL_PTB = r"""import logging
import os

from telegram import Update
from telegram.ext import Application, CommandHandler, ContextTypes, MessageHandler, filters

logging.basicConfig(level=logging.INFO)
logging.getLogger('httpx').setLevel(logging.WARNING)  # httpx would print your token in URLs


async def start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await update.message.reply_text('Hello! I am running on Bot Hosting Manager 🚀')


async def echo(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await update.message.reply_text(update.message.text)


def main() -> None:
    token = os.environ.get('BOT_TOKEN')
    if not token:
        raise SystemExit('BOT_TOKEN is not set - use the 🔑 Bot token button in the manager.')
    app = Application.builder().token(token).build()
    app.add_handler(CommandHandler('start', start))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, echo))
    app.run_polling()


main()
"""
TPL_AIOGRAM = r"""import asyncio
import logging
import os

from aiogram import Bot, Dispatcher
from aiogram.filters import CommandStart
from aiogram.types import Message

logging.basicConfig(level=logging.INFO)
dp = Dispatcher()


@dp.message(CommandStart())
async def start(message: Message) -> None:
    await message.answer('Hello! I am running on Bot Hosting Manager 🚀')


@dp.message()
async def echo(message: Message) -> None:
    if message.text:
        await message.answer(message.text)


async def main() -> None:
    token = os.environ.get('BOT_TOKEN')
    if not token:
        raise SystemExit('BOT_TOKEN is not set - use the 🔑 Bot token button in the manager.')
    await dp.start_polling(Bot(token))


asyncio.run(main())
"""
TPL_DEMO = r"""import sys
import time

print('Demo started. Use ⌨️ Send Command to type to me; I read stdin.', flush=True)
counter = 0
import threading


def heartbeat() -> None:
    global counter
    while True:
        counter += 1
        print(f'heartbeat #{counter}', flush=True)
        time.sleep(10)


threading.Thread(target=heartbeat, daemon=True).start()
for line in sys.stdin:
    line = line.strip()
    print(f'you said: {line}', flush=True)
    if line == 'crash':
        raise RuntimeError('requested crash (tests keep-alive)')
"""
TEMPLATES = {
    "ptb": ("🤖 python-telegram-bot", "Echo bot (needs a token)",
            {"app.py": TPL_PTB, "requirements.txt": "python-telegram-bot>=21.0\n"}),
    "aiogram": ("⚡ aiogram 3", "Echo bot (needs a token)",
                {"app.py": TPL_AIOGRAM, "requirements.txt": "aiogram>=3.0\n"}),
    "demo": ("🧪 Console demo", "Heartbeat + stdin echo; type 'crash' to test keep-alive", {"app.py": TPL_DEMO}),
}


async def h_tpl(update, context, user, args) -> None:
    if not args:
        rows = [[btn(t[0], f"tp:{k}")] for k, t in TEMPLATES.items()] + [BACK_MENU]
        listing = "\n".join(f"{t[0]} — {t[1]}" for t in TEMPLATES.values())
        return await reply(update, f"🧩 <b>Templates</b>\nCreate a ready-to-run project in one tap:\n\n{listing}", kb(rows))
    t = TEMPLATES.get(args[0])
    if not t:
        return
    if DB.count_projects(user["id"]) >= PROJECTS.user_limit(user):
        return await reply(update, f"❌ Project limit reached ({PROJECTS.user_limit(user)}).", kb([BACK_MENU]))
    p = PROJECTS.create(user["id"], PROJECTS.unique_name(user["id"], clean_name(t[0].split(" ", 1)[1])))
    src = PROJECTS.src_dir(p)
    for fname, content in t[2].items():
        atomic_write(src / fname, content.encode("utf-8"))
    DB.update_project(p["id"], startup="app.py")
    rows = []
    if args[0] != "demo":
        rows.append([btn("🔑 Set bot token", f"se:{p['id']}:tk")])
    if "requirements.txt" in t[2]:
        rows.append([btn("📦 Install requirements", f"pp:{p['id']}:r")])
    rows.append([btn("▶️ Start", f"pk:start:{p['id']}"), btn("📂 Dashboard", f"pd:{p['id']}")])
    steps = ("1️⃣ Set your bot token  2️⃣ Install requirements  3️⃣ Start" if args[0] != "demo" else "Just press Start!")
    await reply(update, f"✅ <b>{esc(p['name'])}</b> created (#{p['id']}).\n{steps}", kb(rows))


# ------------------------------------------------------------- update files (keeps data)
async def act_update(update, context, user, p) -> None:
    set_await(context, "update_files", 600, pid=p["id"])
    await reply(update,
                f"🔁 <b>Update {esc(p['name'])}</b>\nSend a <b>.zip</b> (merged into the project) or a single <b>.py</b> file.\n\n"
                "• 🛡 Your data is kept: existing <code>.db .sqlite .json .session</code> files and "
                "<code>data/ storage/ sessions/</code> folders are never overwritten.\n"
                "• 💾 A backup is taken first.\n"
                "• ♻️ If the bot was running it restarts automatically with the new code.",
                kb([[btn("❌ Cancel", f"pd:{p['id']}")]]))


async def update_project_files(update, context, user, st, doc) -> None:
    p = owned(user, st["pid"])
    m = update.effective_message
    if not p:
        return
    fname = os.path.basename((doc.file_name or "").replace("\\", "/"))
    is_zip = fname.lower().endswith(".zip")
    if not (is_zip or (fname.lower().endswith(".py") and valid_filename(fname))):
        return await m.reply_text("❌ Send a .zip or a .py file (or /cancel).")
    if (doc.file_size or 0) > CFG.max_zip_mb * 1048576:
        return await m.reply_text(f"❌ File larger than {CFG.max_zip_mb} MB.")
    clear_await(context)
    was_active = bool(p["desired"]) or p["status"] == "running"
    status = await m.reply_text("⏳ <b>Updating…</b>\n⏳ Downloading…", parse_mode=HTML)
    tmp = CFG.d_tmp / f"upd_{p['id']}_{int(time.time() * 1000)}"
    src = PROJECTS.src_dir(p)
    try:
        f = await doc.get_file()
        await f.download_to_drive(str(tmp))
        await safe_edit(status, "⏳ <b>Updating…</b>\n✅ Downloaded\n⏳ Backing up current files…")
        await PROJECTS.backup(p)
        kept = n = 0
        if is_zip:
            prog: dict = {"done": 0, "total": 0, "bytes": 0}
            stop = asyncio.Event()
            updater = asyncio.create_task(progress_loop(status, prog, stop, "⏳ <b>Updating…</b>"))
            try:
                n = await asyncio.get_running_loop().run_in_executor(
                    None, lambda: safe_extract(tmp, src, prog, keep=keep_data))
            finally:
                stop.set()
                await updater
            kept = prog.get("kept", 0)
        else:
            target = safe_join(src, fname)
            if target.exists() and keep_data([fname]):
                kept = 1
            else:
                shutil.move(str(tmp), target)
                os.chmod(target, 0o644)
                n = 1
            if not p["startup"]:
                DB.update_project(p["id"], startup=fname)
        extra = ""
        if was_active:
            await safe_edit(status, "⏳ <b>Updating…</b>\n✅ Files updated\n♻️ Restarting the bot…")
            ok, info = await PM.restart(p)
            extra = f"\n{'✅' if ok else '❌'} Restart: {esc(info)}"
        p2 = PM.fresh(p["id"])
        await safe_edit(status, f"✅ <b>Update complete</b> — {n} file(s) written, 🛡 {kept} data file(s) kept untouched."
                                f"{extra}\n\n{project_card(p2)}", dash_markup(p2))
    except ZipError as e:
        await safe_edit(status, f"❌ Update refused: {esc(e)}\nYour files were not changed (backup kept).", kb([BACK_MENU]))
    except Exception as e:
        log.exception("update failed")
        await safe_edit(status, f"❌ Update failed: {esc(e)}", kb([BACK_MENU]))
    finally:
        tmp.unlink(missing_ok=True)


# ------------------------------------------------------------- backups
def _bk_ts(path: Path) -> str:
    try:
        return ts_str(int(path.stem.rsplit("_", 1)[1]))
    except (IndexError, ValueError):
        return path.name


async def act_backup(update, context, user, p) -> None:
    files = PROJECTS.backup_files(p)[:5]
    pid = p["id"]
    rows = [[btn("💾 Create backup now", f"bk:{pid}:mk")]]
    for i, f in enumerate(files):
        rows.append([btn(f"⬇️ {_bk_ts(f)} · {human_bytes(f.stat().st_size)}", f"bk:{pid}:dl:{i}"),
                     btn("↩️ Restore", f"bk:{pid}:rs:{i}")])
    rows.append([btn("📂 Dashboard", f"pd:{pid}"), btn("🏠 Menu", "mm")])
    auto = f"every {CFG.auto_backup_hours}h" if CFG.auto_backup_hours else "off"
    await reply(update, f"💾 <b>Backups — {esc(p['name'])}</b>\nStored on the server (last {CFG.backup_keep}). "
                f"Automatic backups: <b>{auto}</b>. Backups contain project files only.\n"
                f"{'<i>No backups yet.</i>' if not files else ''}", kb(rows))


async def send_backup(context, chat_id: int, path: Path) -> None:
    if path.stat().st_size > 45 * 1048576:
        await context.bot.send_message(chat_id, "ℹ️ Backup is larger than Telegram's 45 MB limit; it is stored on the server.")
        return
    with open(path, "rb") as fh:
        await context.bot.send_document(chat_id, document=fh, filename=path.name, caption="💾 Project backup")


async def h_bk(update, context, user, args) -> None:
    p = owned(user, args[0])
    if not p:
        return await reply(update, "⚠️ Project not found.", kb([BACK_MENU]))
    op = args[1]
    chat_id = update.effective_chat.id
    files = PROJECTS.backup_files(p)
    if op == "mk":
        path = await PROJECTS.backup(p)
        if not path:
            return await update.callback_query.answer("Backup failed.", show_alert=True)
        await send_backup(context, chat_id, path)
        return await act_backup(update, context, user, p)
    try:
        f = files[int(args[2])]
    except (IndexError, ValueError):
        return await update.callback_query.answer("Backup list changed - reopen.", show_alert=True)
    if op == "dl":
        return await send_backup(context, chat_id, f)
    if op == "rs":
        return await reply(update, f"↩️ Restore <b>{esc(p['name'])}</b> from backup <code>{_bk_ts(f)}</code>?\n"
                           "Current files are replaced (a fresh backup of them is taken first).",
                           kb([[btn("✅ Yes, restore", f"bk:{p['id']}:rsy:{args[2]}"), btn("❌ No", f"pk:backup:{p['id']}")]]))
    if op == "rsy":
        was_active = bool(p["desired"]) or p["status"] == "running"
        msg = await reply(update, "⏳ Restoring…")
        if p["status"] == "running":
            await PM.stop(p)
        await PROJECTS.backup(p)
        f = PROJECTS.backup_files(p)[int(args[2]) + 1] if len(PROJECTS.backup_files(p)) > int(args[2]) + 1 else f
        try:
            n = await PROJECTS.restore(p, f)
        except ZipError as e:
            return await safe_edit(msg, f"❌ Restore failed: {esc(e)}", kb([BACK_MENU]))
        extra = ""
        if was_active:
            ok, info = await PM.start(DB.project(p["id"]))  # type: ignore
            extra = f"\n{'✅' if ok else '❌'} Restart: {esc(info)}"
        await safe_edit(msg, f"✅ Restored {n} files.{extra}", kb([[btn("📂 Dashboard", f"pd:{p['id']}")], BACK_MENU]))


# ------------------------------------------------------------- bot token setter
async def handle_token_set(update, context, user, st, text: str) -> None:
    p = owned(user, st["pid"])
    clear_await(context)
    chat_id = update.effective_chat.id
    try:
        await update.effective_message.delete()  # never leave the token in the chat
    except TelegramError:
        pass
    if not p:
        return
    retry = kb([[btn("🔁 Try again", f"se:{p['id']}:tk"), btn("📂 Dashboard", f"pd:{p['id']}")]])
    token = text.strip()
    if not TOKEN_RE.match(token):
        return await context.bot.send_message(chat_id, "❌ That does not look like a bot token "
                                              "(format <code>123456:ABC…</code>).", parse_mode=HTML, reply_markup=retry)
    who = "could not verify (network)"
    try:
        from telegram import Bot
        async with Bot(token) as b:
            me = await asyncio.wait_for(b.get_me(), 15)
        who = f"@{me.username}"
    except InvalidToken:
        return await context.bot.send_message(chat_id, "❌ Telegram rejected this token.", reply_markup=retry)
    except Exception:
        pass
    DB.env_set(p["id"], "BOT_TOKEN", token)
    extra = ""
    p = PM.fresh(p["id"])
    if p and p["status"] == "running":
        ok, info = await PM.restart(p)
        extra = f"\n{'✅ Restarted with the new token.' if ok else '❌ Restart failed: ' + esc(info)}"
    await context.bot.send_message(chat_id, f"✅ Token saved for <b>{esc(who)}</b> (encrypted).{extra}", parse_mode=HTML,
                                   reply_markup=kb([[btn("▶️ Start", f"pk:start:{p['id']}"),
                                                     btn("📂 Dashboard", f"pd:{p['id']}")]]))


async def handle_args_set(update, context, user, st, text: str) -> None:
    p = owned(user, st["pid"])
    clear_await(context)
    if not p:
        return
    raw = text.strip()
    if raw in ("-", "none", ""):
        raw = ""
    try:
        toks = shlex.split(raw) if raw else []
        if len(toks) > 20 or any(len(t) > 200 or "\x00" in t for t in toks):
            raise ValueError("too many or too long arguments")
    except ValueError as e:
        return await update.effective_message.reply_text(f"❌ Invalid arguments: {esc(e)}", parse_mode=HTML)
    DB.update_project(p["id"], args=raw or None)
    await update.effective_message.reply_text(
        f"✅ Arguments {'set to <code>' + esc(raw) + '</code>' if raw else 'cleared'}. Restart to apply.",
        parse_mode=HTML, reply_markup=kb([[btn("🔄 Restart", f"pk:restart:{p['id']}"), btn("⚙️ Settings", f"pk:set:{p['id']}")]]))


# ------------------------------------------------------------- log search
def hits_view(p: sqlite3.Row, title: str, hits: list[str]) -> tuple[str, InlineKeyboardMarkup]:
    body, shown = fit_tail(hits, 3300)
    pid = p["id"]
    text = (f"{title} — <b>{esc(p['name'])}</b>\n{len(hits)} matching line(s)"
            f"{f' (showing last {shown})' if shown < len(hits) else ''}\n"
            + (f"<pre>{esc(body)}</pre>" if body else "<i>No matches.</i>"))
    return text, kb([[btn("🔍 Search again", f"ls:{pid}"), btn("🚨 Errors", f"le:{pid}")],
                     [btn("📟 Live logs", f"lv:{pid}:100:1"), btn("📂 Dashboard", f"pd:{pid}")]])


async def h_ls(update, context, user, args) -> None:
    p = owned(user, args[0])
    if not p:
        return
    set_await(context, "log_search", 300, pid=p["id"])
    await reply(update, f"🔍 Send the text to search for in the logs of <b>{esc(p['name'])}</b> "
                "(case-insensitive, last ~20 000 lines).", kb([[btn("❌ Cancel", f"pd:{p['id']}")]]))


async def h_le(update, context, user, args) -> None:
    p = owned(user, args[0])
    if not p:
        return
    clear_await(context)
    text, markup = hits_view(p, "🚨 Errors", LOGS.error_lines(p))
    await reply(update, text, markup)


async def handle_log_search(update, context, user, st, text: str) -> None:
    p = owned(user, st["pid"])
    clear_await(context)
    if not p or not text.strip():
        return
    hits = LOGS.search(p, text.strip()[:100])
    t, markup = hits_view(p, f"🔍 “{esc(text.strip()[:40])}”", hits)
    await update.effective_message.reply_text(t, parse_mode=HTML, reply_markup=markup)


async def cmd_projects(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user = await guard(update, context)
    if user:
        text, markup = projects_view(user)
        await update.effective_message.reply_text(text, parse_mode=HTML, reply_markup=markup)  # type: ignore


async def cmd_ping(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user = await guard(update, context)
    if user:
        await update.effective_message.reply_text(  # type: ignore
            f"🏓 Pong! Manager uptime <b>{human_dur(time.time() - START_TIME)}</b> · "
            f"{len(DB.projects_by_status('running'))} project(s) running.", parse_mode=HTML)


# ============================================================================
# 13. ADMIN COMMANDS
# ============================================================================
def admin_only(fn):
    async def wrapper(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
        u = update.effective_user
        if not u or not is_admin(u.id) or update.effective_chat.type != "private":
            return
        await fn(update, context)
    return wrapper


def _int_arg(context, i: int = 0) -> Optional[int]:
    try:
        return int(context.args[i])
    except (IndexError, ValueError):
        return None


ADMIN_HELP = ("👑 <b>Admin commands</b>\n"
              "/users — list users\n/adduser &lt;id&gt; — approve a user\n/ban &lt;id&gt; · /unban &lt;id&gt;\n"
              "/setlimit &lt;id&gt; &lt;n&gt; — project limit\n/allprojects — every project\n"
              "/killproject &lt;project_id&gt; — force-kill\n/stopall — stop all projects\n"
              "/broadcast &lt;text&gt; — message all users")


def admin_users_text() -> str:
    lines = []
    for u in DB.users():
        lines.append(f"<code>{u['id']}</code> @{esc(u['username'] or '-')} · projects {DB.count_projects(u['id'])}"
                     f"{'' if u['approved'] else ' · pending'}{' · BANNED' if u['banned'] else ''}"
                     f"{' · limit ' + str(u['max_projects']) if u['max_projects'] is not None else ''}")
    return "\n".join(lines)[:3800] or "No users."


def admin_projects_text() -> str:
    lines = []
    for r in DB.all_projects():
        p = PM.fresh(r["id"])
        lines.append(f"#{p['id']} {STATUS_ICON.get(p['status'], '⚪')} <b>{esc(p['name'])}</b> · owner "
                     f"<code>{p['owner_id']}</code> · {p['status']}")
    return "\n".join(lines)[:3800] or "No projects."


async def h_admin_panel(update, context, user, args) -> None:
    if not is_admin(user["id"]):
        return
    op = args[0] if args else "m"
    back = kb([[btn("👑 Admin", "ad"), btn("🏠 Menu", "mm")]])
    if op == "users":
        return await reply(update, "👥 <b>Users</b>\n" + admin_users_text(), back)
    if op == "proj":
        return await reply(update, "📦 <b>All projects</b>\n" + admin_projects_text(), back)
    if op == "stopall":
        n = 0
        for r in DB.projects_by_status("running"):
            ok, _ = await PM.stop(r)
            n += int(ok)
        return await reply(update, f"⏹ Stopped {n} project(s) (they will not auto-resume).", back)
    if op == "resume":
        spawn(resume_projects(context.application, initial=False))
        return await reply(update, "▶️ Resuming every project that should be running…", back)
    if op == "bkdb":
        backup_database()
        return await reply(update, "💾 Database backup written to the backups folder.", back)
    projs = DB.all_projects()
    running = len(DB.projects_by_status("running"))
    await reply(update, f"{ADMIN_HELP}\n\nUsers: {len(DB.users())} · projects: {len(projs)} · running: {running}",
                kb([[btn("👥 Users", "ad:users"), btn("📦 All projects", "ad:proj")],
                    [btn("⏹ Stop all", "ad:stopall"), btn("▶️ Resume all", "ad:resume")],
                    [btn("💾 Backup database", "ad:bkdb")], BACK_MENU]))


@admin_only
async def cmd_admin(update, context) -> None:
    await update.effective_message.reply_text(ADMIN_HELP, parse_mode=HTML)


@admin_only
async def cmd_users(update, context) -> None:
    lines = []
    for u in DB.users():
        lines.append(f"<code>{u['id']}</code> @{esc(u['username'] or '-')} · projects {DB.count_projects(u['id'])}"
                     f"{'' if u['approved'] else ' · pending'}{' · BANNED' if u['banned'] else ''}"
                     f"{' · limit ' + str(u['max_projects']) if u['max_projects'] is not None else ''}")
    await update.effective_message.reply_text("\n".join(lines)[:4000] or "No users.", parse_mode=HTML)


@admin_only
async def cmd_adduser(update, context) -> None:
    uid = _int_arg(context)
    if uid is None:
        return await update.effective_message.reply_text("Usage: /adduser <telegram_id>")
    DB.x("INSERT OR IGNORE INTO users(id,first_seen,approved) VALUES(?,?,1)", (uid, time.time()))
    DB.set_user(uid, approved=1, banned=0)
    await update.effective_message.reply_text(f"✅ User {uid} approved.")


async def _stop_user_projects(uid: int) -> None:
    for r in DB.projects_of(uid):
        await PM.stop(r, force=True)


@admin_only
async def cmd_ban(update, context) -> None:
    uid = _int_arg(context)
    if uid is None or is_admin(uid):
        return await update.effective_message.reply_text("Usage: /ban <telegram_id> (admins cannot be banned)")
    DB.set_user(uid, banned=1)
    await _stop_user_projects(uid)
    await update.effective_message.reply_text(f"🚫 User {uid} banned and their projects stopped.")


@admin_only
async def cmd_unban(update, context) -> None:
    uid = _int_arg(context)
    if uid is None:
        return await update.effective_message.reply_text("Usage: /unban <telegram_id>")
    DB.set_user(uid, banned=0)
    await update.effective_message.reply_text(f"✅ User {uid} unbanned.")


@admin_only
async def cmd_setlimit(update, context) -> None:
    uid, n = _int_arg(context, 0), _int_arg(context, 1)
    if uid is None or n is None or n < 0:
        return await update.effective_message.reply_text("Usage: /setlimit <telegram_id> <max_projects>")
    DB.set_user(uid, max_projects=n)
    await update.effective_message.reply_text(f"✅ Limit for {uid} set to {n}.")


@admin_only
async def cmd_allprojects(update, context) -> None:
    lines = []
    for r in DB.all_projects():
        p = PM.fresh(r["id"])
        lines.append(f"#{p['id']} {STATUS_ICON.get(p['status'], '⚪')} <b>{esc(p['name'])}</b> · owner "
                     f"<code>{p['owner_id']}</code> · {p['status']}")
    await update.effective_message.reply_text("\n".join(lines)[:4000] or "No projects.", parse_mode=HTML)


@admin_only
async def cmd_killproject(update, context) -> None:
    pid = _int_arg(context)
    p = PM.fresh(pid) if pid is not None else None
    if not p:
        return await update.effective_message.reply_text("Usage: /killproject <project_id>")
    ok, info = await PM.stop(p, force=True)
    await update.effective_message.reply_text(f"{'✅' if ok else 'ℹ️'} #{pid}: {info}")


@admin_only
async def cmd_stopall(update, context) -> None:
    n = 0
    for r in DB.projects_by_status("running"):
        ok, _ = await PM.stop(r)
        n += int(ok)
    await update.effective_message.reply_text(f"⏹ Stopped {n} project(s).")


@admin_only
async def cmd_broadcast(update, context) -> None:
    text = " ".join(context.args or [])
    if not text:
        return await update.effective_message.reply_text("Usage: /broadcast <text>")
    sent = 0
    for u in DB.users():
        if u["approved"] and not u["banned"]:
            try:
                await context.bot.send_message(u["id"], f"📢 {text}")
                sent += 1
            except TelegramError:
                pass
            await asyncio.sleep(0.05)
    await update.effective_message.reply_text(f"Sent to {sent} user(s).")


# ============================================================================
# 14. BACKGROUND MONITOR (crash detection, notifications, auto-restart)
# ============================================================================
async def notify(app: Application, uid: int, text: str, markup=None) -> None:
    try:
        await app.bot.send_message(uid, text, parse_mode=HTML, reply_markup=markup)
    except TelegramError as e:
        log.debug("notify failed: %s", e)


_BG: set = set()


def spawn(coro) -> asyncio.Task:
    """create_task that keeps a strong reference until the task is done."""
    t = asyncio.create_task(coro)
    _BG.add(t)
    t.add_done_callback(_BG.discard)
    return t


async def after_exit(app: Application, pid: int) -> None:
    """Keep-alive: notify the owner and restart crashed projects with exponential back-off."""
    p = DB.project(pid)
    if not p:
        return
    err = LOGS.last_error(p)
    code = p["exit_code"]
    if p["status"] == "stopped" and code == 0:
        await notify(app, p["owner_id"], f"✅ <b>{esc(p['name'])}</b> finished (exit code 0).",
                     kb([[btn("📟 Logs", f"lv:{pid}:50:0")]]))
        return
    text = (f"🔴 <b>{esc(p['name'])}</b> stopped unexpectedly (exit code "
            f"{code if code is not None else 'unknown'}).")
    if err:
        text += f"\n<code>{esc(err)}</code>"
    n = p["restart_count"]
    if p["auto_restart"] and n < CFG.auto_restart_max:
        delay = min(60, 3 * 2 ** n)
        DB.update_project(pid, restart_count=n + 1, total_restarts=(p["total_restarts"] or 0) + 1)
        await notify(app, p["owner_id"], text + f"\n♻️ Keep-alive: restarting in {delay}s "
                                                f"(attempt {n + 1}/{CFG.auto_restart_max})…")
        await asyncio.sleep(delay)
        cur = DB.project(pid)
        if not cur or cur["status"] == "running" or not cur["desired"]:
            return  # the user started/stopped it meanwhile
        ok, info = await PM.start(cur, manual=False)
        await notify(app, p["owner_id"], f"{'✅' if ok else '❌'} {esc(p['name'])}: {esc(info)}",
                     kb([[btn("📟 Logs", f"lv:{pid}:50:1"), btn("📂 Dashboard", f"pd:{pid}")]]))
    else:
        if p["auto_restart"]:
            text += "\n⛔ Auto-restart limit reached - it will be retried after the next manager restart."
        await notify(app, p["owner_id"], text,
                     kb([[btn("📟 Logs", f"lv:{pid}:50:0"), btn("▶️ Start", f"pk:start:{pid}")]]))


async def resume_projects(app: Application, initial: bool = True) -> None:
    """Start every project that was running before the manager/server went down."""
    if initial:
        if not CFG.resume_on_start:
            return
        await asyncio.sleep(3)
    rows = [r for r in DB.all_projects() if r["desired"] and r["auto_restart"] and r["status"] != "running"]
    if not rows:
        return
    ok_n, failed = 0, []
    for r in rows:
        p = DB.project(r["id"])
        if not p or PM.is_alive(p) or not p["desired"]:
            continue
        DB.update_project(p["id"], restart_count=0)
        ok, info = await PM.start(p, manual=False)
        if ok:
            ok_n += 1
            await notify(app, p["owner_id"], f"♻️ <b>{esc(p['name'])}</b> was auto-resumed after the server/manager "
                                             f"restarted. Your files and data are intact.",
                         kb([[btn("📟 Logs", f"lv:{p['id']}:50:1"), btn("📂 Dashboard", f"pd:{p['id']}")]]))
        else:
            failed.append(f"#{p['id']} {p['name']}: {info.splitlines()[0][:80]}")
            await notify(app, p["owner_id"], f"❌ Could not auto-resume <b>{esc(p['name'])}</b>:\n{esc(info)}")
        await asyncio.sleep(2)  # stagger to avoid a CPU spike
    summary = f"♻️ Auto-resume finished: {ok_n} started, {len(failed)} failed."
    if failed:
        summary += "\n" + "\n".join(esc(f) for f in failed)
    for aid in CFG.admin_ids:
        await notify(app, aid, summary)


async def scheduled_restart(app: Application, pid: int) -> None:
    p = DB.project(pid)
    if not p or p["status"] != "running" or PM.lock(pid).locked():
        return
    ok, info = await PM.restart(p)
    await notify(app, p["owner_id"], f"⏰ Scheduled restart of <b>{esc(p['name'])}</b>: "
                                     f"{'✅ ok' if ok else '❌ ' + esc(info)}")


async def auto_backup_all() -> None:
    for p in DB.all_projects():
        files = PROJECTS.backup_files(p)
        if not files or time.time() - files[0].stat().st_mtime > CFG.auto_backup_hours * 3600:
            await PROJECTS.backup(p)


async def monitor_loop(app: Application) -> None:
    last_backup = 0.0
    while True:
        try:
            await asyncio.sleep(CFG.monitor_interval)
            for p in DB.projects_by_status("running"):
                if PM.is_alive(p):
                    LOGS.trim_running(p)
                    up = time.time() - (p["started_at"] or time.time())
                    if p["restart_count"] and up > 600:
                        DB.update_project(p["id"], restart_count=0)
                    if p["restart_every_h"] and up > p["restart_every_h"] * 3600:
                        spawn(scheduled_restart(app, p["id"]))
                else:
                    PM.finalize(p["id"])
            while PM.pending:
                spawn(after_exit(app, PM.pending.pop(0)))  # never block the monitor on back-off delays
            if CFG.auto_backup_hours and time.time() - last_backup > 900:
                last_backup = time.time()
                spawn(auto_backup_all())
        except asyncio.CancelledError:
            raise
        except Exception:
            log.exception("monitor error")


# ============================================================================
# 15. MAIN STARTUP
# ============================================================================
ROUTES: dict[str, HandlerFn] = {
    "mm": h_menu, "hp": h_help, "st": h_status, "cx": h_cancel, "up": h_up, "us": h_us,
    "pa": h_pick, "pk": h_pk, "lv": h_lv, "ld": h_ld, "ch": h_ch, "hr": h_hr,
    "pp": h_pp, "fm": h_fm, "fa": h_fa, "se": h_se, "sf": h_sf, "ev": h_ev, "ad": h_admin_panel,
    "pl": h_projects, "pd": h_pd, "tp": h_tpl, "bk": h_bk, "ls": h_ls, "le": h_le,
}
ACTIONS: dict[str, HandlerFn] = {
    "start": act_start, "stop": act_stop, "restart": act_restart, "logs": act_logs,
    "cmd": act_cmd, "files": act_files, "pip": act_pip, "dlog": act_dlog, "set": act_set,
    "dash": act_dash, "update": act_update, "backup": act_backup,
}


async def on_error(update: object, context: ContextTypes.DEFAULT_TYPE) -> None:
    log.error("Unhandled error", exc_info=context.error)
    if isinstance(update, Update) and update.effective_chat:
        try:
            await context.bot.send_message(update.effective_chat.id,
                                           "⚠️ Internal error. It has been logged; please try again.")
        except TelegramError:
            pass


async def post_init(app: Application) -> None:
    await app.bot.set_my_commands([
        BotCommand("start", "Main menu"), BotCommand("projects", "My projects"), BotCommand("status", "Server status"),
        BotCommand("ping", "Is the manager alive?"),
        BotCommand("cancel", "Cancel current input"), BotCommand("help", "Help")])
    # Recover metadata: re-adopt still-running processes, finalize the ones that died.
    adopted = lost = 0
    for p in DB.projects_by_status("running"):
        if pid_alive(p["pid"], p["pid_ctime"]):
            adopted += 1
        else:
            PM.finalize(p["id"])
            lost += 1
    log.info("Recovery: %d project(s) still running, %d exited while manager was down", adopted, lost)
    if SANDBOX.docker:
        asyncio.create_task(prepare_docker_image())
    app.bot_data["monitor"] = asyncio.create_task(monitor_loop(app))
    spawn(resume_projects(app))  # bring back everything that was running before
    me = await app.bot.get_me()
    log.info("Bot @%s started (sandbox=%s, data=%s)", me.username, SANDBOX.mode, CFG.data_dir)


async def prepare_docker_image() -> None:
    rc, _ = await run_exec([CFG.docker_bin, "image", "inspect", CFG.docker_image], timeout=30)
    if rc != 0:
        log.info("Pulling Docker image %s …", CFG.docker_image)
        rc, out = await run_exec([CFG.docker_bin, "pull", CFG.docker_image], timeout=900)
        if rc != 0:
            log.error("docker pull failed: %s", out[-300:])


async def post_shutdown(app: Application) -> None:
    t = app.bot_data.get("monitor")
    if t:
        t.cancel()
    for t in list(LIVE.values()):
        t.cancel()
    log.info("Manager stopped. Hosted projects keep running in the background.")


def backup_database() -> None:
    try:
        if CFG.db_path.exists() and CFG.db_path.stat().st_size:
            dest = CFG.d_backups / f"hostmgr-{time.strftime('%Y%m%d-%H%M%S')}.sqlite3"
            shutil.copy2(CFG.db_path, dest)
            for old in sorted(CFG.d_backups.glob("hostmgr-*.sqlite3"))[:-5]:
                old.unlink(missing_ok=True)
    except OSError:
        pass


def init_services() -> None:
    global DB, SECRETS, SANDBOX, PROJECTS, LOGS, PKG, PM
    backup_database()
    SECRETS = Secrets()
    DB = Database(CFG.db_path)
    SANDBOX = Sandbox()
    PROJECTS = Projects()
    LOGS = LogManager()
    PKG = PackageManager()
    PM = ProcessManager()
    for uid in CFG.admin_ids | CFG.allowed_users:
        DB.x("INSERT OR IGNORE INTO users(id,first_seen,approved) VALUES(?,?,1)", (uid, time.time()))
        DB.set_user(uid, approved=1)


def build_application() -> Application:
    app = (Application.builder().token(CFG.bot_token)
           .concurrent_updates(True)
           .connect_timeout(20).read_timeout(60).write_timeout(120).pool_timeout(30)
           .post_init(post_init).post_shutdown(post_shutdown).build())
    for name, fn in (("start", cmd_start), ("menu", cmd_start), ("help", cmd_help), ("status", cmd_status),
                     ("cancel", cmd_cancel), ("admin", cmd_admin), ("users", cmd_users), ("adduser", cmd_adduser),
                     ("projects", cmd_projects), ("ping", cmd_ping),
                     ("ban", cmd_ban), ("unban", cmd_unban), ("setlimit", cmd_setlimit),
                     ("allprojects", cmd_allprojects), ("killproject", cmd_killproject),
                     ("stopall", cmd_stopall), ("broadcast", cmd_broadcast)):
        app.add_handler(CommandHandler(name, fn))
    app.add_handler(CallbackQueryHandler(on_callback))
    app.add_handler(MessageHandler(filters.Document.ALL & filters.ChatType.PRIVATE, on_document))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND & filters.ChatType.PRIVATE, on_text))
    app.add_error_handler(on_error)
    return app


def main() -> None:
    global CFG
    load_env_file(BASE_DIR / ".env")
    load_env_file(Path.cwd() / ".env")
    logging.basicConfig(format="%(asctime)s %(levelname)s %(name)s: %(message)s", level=logging.INFO)
    # httpx logs full request URLs at INFO level, which contain the bot token. Silence it.
    for noisy in ("httpx", "httpcore", "telegram.ext.Application"):
        logging.getLogger(noisy).setLevel(logging.WARNING)
    CFG = Config()
    if not sys.platform.startswith("linux"):
        sys.exit("This application requires Linux (named pipes, process groups, Docker).")
    if not CFG.bot_token:
        sys.exit("BOT_TOKEN is not set. Create a .env file (see instructions) or export BOT_TOKEN.")
    if not CFG.admin_ids:
        sys.exit("ADMIN_IDS is not set. Put your numeric Telegram user id in ADMIN_IDS.")
    try:
        CFG.ensure_dirs()
        init_services()
    except Exception as e:
        sys.exit(f"Startup failed while preparing data directory/database: {e}")
    ok, msg = SANDBOX.check()
    if not ok:
        sys.exit(f"Sandbox check failed: {msg}")
    if not SANDBOX.docker:
        log.warning("SANDBOX_MODE=process: hosted code is NOT isolated. Only admins may run projects "
                    "(ALLOW_UNSANDBOXED_USERS=false).")
    app = build_application()
    try:
        app.run_polling(allowed_updates=Update.ALL_TYPES, drop_pending_updates=False)
    except InvalidToken:
        sys.exit("Telegram rejected BOT_TOKEN (invalid token).")
    except TelegramError as e:
        sys.exit(f"Telegram error on startup: {e}")
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    main()
