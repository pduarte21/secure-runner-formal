#!/usr/bin/env bash
set -euo pipefail

# --------------------------------------------------
# Secure Runner — TLA+ TLC Runner
# --------------------------------------------------

# -------- Paths --------
ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TLC_JAR="$ROOT_DIR/tools/tlc/tla2tools.jar"
JAVA_HEAP="${JAVA_HEAP:-8G}"
JAVA_GC="${JAVA_GC:--XX:+UseParallelGC}"
TLC_WORKERS="${TLC_WORKERS:-auto}"
DEFAULT_OUT="$ROOT_DIR/tlc_outputs"

# -------- Helpers --------
usage() {
  cat <<EOF
Usage:
  $0 run   -s SPEC -c CFG [-o OUT] [-- ARGS]
  $0 clean
  $0 help

Commands:
  run     Run TLC on a TLA+ spec with a given config
  clean   Remove TLC outputs
  help    Show this message

Options (run):
  -s SPEC   Path to .tla specification
  -c CFG    Path to .cfg model configuration
  -o OUT    Output directory (default: tlc_outputs)

Examples:
  $0 run -s model/SecureRunnerHardenedModel.tla -c models/configs/liveness.cfg
  $0 run -s model/SecureRunnerHardenedModel.tla   -c models/configs/liveness.cfg -- -deadlock
EOF
}

fatal() {
  echo "[!] $1" >&2
  exit 1
}

info() {
  echo "[+] $1"
}

# -------- Checks --------
check_tlc() {
  [[ -f "$TLC_JAR" ]] || fatal "TLC jar not found at $TLC_JAR"
  command -v java >/dev/null 2>&1 || fatal "Java not found (Java 11+ required)"
}

# -------- Commands --------
COMMAND="${1:-help}"
shift || true

case "$COMMAND" in
  run)
    SPEC=""
    CFG=""
    OUT="$DEFAULT_OUT"

    while [[ $# -gt 0 ]]; do
      case "$1" in
        -s) SPEC="$2"; shift 2 ;;
        -c) CFG="$2"; shift 2 ;;
        -o) OUT="$2"; shift 2 ;;
        --) shift; break ;;
        *) fatal "Unknown option: $1" ;;
      esac
    done

    [[ -n "$SPEC" ]] || fatal "Missing -s SPEC"
    [[ -n "$CFG"  ]] || fatal "Missing -c CFG"
    [[ -f "$SPEC" ]] || fatal "Spec not found: $SPEC"
    [[ -f "$CFG"  ]] || fatal "Config not found: $CFG"

    check_tlc
    mkdir -p "$OUT"

    info "Running TLC"
    info "  Spec   : $SPEC"
    info "  Config : $CFG"
    info "  Output : $OUT"

    java \
      -Xmx"$JAVA_HEAP" \
      "$JAVA_GC" \
      -cp "$TLC_JAR" \
      tlc2.TLC \
      -workers "$TLC_WORKERS" \
      -checkpoint 15 \
      -config "$CFG" \
      -metadir "$OUT" \
      "$@" \
      "$SPEC"

    info "TLC completed successfully"
    ;;

  clean)
    info "Cleaning TLC outputs"

    # Remove TLC output directory
    rm -rf "$DEFAULT_OUT"

    info "Cleanup completed"
    ;;


  help|*)
    usage
    ;;
esac
