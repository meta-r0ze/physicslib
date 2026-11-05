#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"

LAKE="${LAKE_BIN:-lake}"

usage() {
  cat <<'USAGE'
Usage:
  ./build.sh                Build libraries, run audits
  ./build.sh all            Same as ./build.sh
  ./build.sh full           Build libraries, run audits, run e8p checks
  ./build.sh build          Build libraries only
  ./build.sh audit          Run audits only
  ./build.sh e8p            Build e8p and run its formatter/reporter checks
  ./build.sh fast <module|file.lean>...
                            Build only OLean artifacts (no C/ilean), e.g.
                            ./build.sh fast PMAction.WallExchange
                            ./build.sh fast src/PMAction/WallExchange.lean
                            FAST_OLD=1 skips transitive dependency checks
  ./build.sh check <file>   Build one module's OLean incrementally
                            e.g. ./build.sh check src/PMConstants/ContentWeight.lean
  ./build.sh lean <file>    Typecheck one file without writing an OLean
  ./build.sh watch <file>   Poll and typecheck one file on every change
  ./build.sh <module>       Build one target, e.g. ./build.sh PMAction
  ./build.sh <file.lean>    Build one file's OLean, e.g. ./build.sh src/PMAction.lean
  ./build.sh help           This text

Set LAKE_BIN to use a non-default lake binary.
Set LEAN_JOBS to control `./build.sh lean` threads (default 4).
USAGE
}

run_audits() {
  local found=0
  while IFS= read -r f; do
    found=$((found + 1))
    echo "== audit: $f =="
    "$LAKE" env lean "$f"
  done < <(find src -type f \( -name 'Audit*.lean' -o -name 'Audit.lean' \) \
             -not -path '*/.lake/*' | sort)
  if [ "$found" -eq 0 ]; then
    echo "No Audit*.lean files found under src/." >&2
    return 1
  fi
}

run_e8p_tests() {
  "$LAKE" build e8p
  "$LAKE" env lean tools/e8p/ConstantsFormatTests.lean
  python3 tools/e8p/tests/constants_report.py .lake/build/bin/e8p
}

case "${1:-all}" in
  help|-h|--help)
    usage
    ;;
  fast)
    shift
    if [ "$#" -eq 0 ]; then
      echo "usage: ./build.sh fast <module>..." >&2
      exit 2
    fi
    old=()
    if [ "${FAST_OLD:-0}" = "1" ]; then old=(--old); fi
    targets=()
    for t in "$@"; do
      if [[ "$t" == +* ]]; then
        targets+=("$t")
      elif [ -f "$t" ] && [[ "$t" == *.lean ]]; then
        targets+=("$t:olean")
      else
        targets+=("+$t:olean")
      fi
    done
    if [ "${#old[@]}" -gt 0 ]; then
      "$LAKE" "${old[@]}" build "${targets[@]}"
    else
      "$LAKE" build "${targets[@]}"
    fi
    ;;
  check)
    shift
    if [ "$#" -eq 0 ]; then
      echo "usage: ./build.sh check <file.lean|Module>" >&2
      exit 2
    fi
    "$LAKE" build "$1:olean"
    ;;
  lean)
    shift
    "$LAKE" env lean -j "${LEAN_JOBS:-4}" "$@"
    ;;
  watch)
    shift
    if [ "$#" -eq 0 ] || [ ! -f "$1" ]; then
      echo "usage: ./build.sh watch <file.lean>" >&2
      exit 2
    fi
    file="$1"
    last="$(cksum "$file")"
    trap 'exit 0' INT TERM
    echo "watching $file (ctrl-c to stop)"
    while true; do
      cur="$(cksum "$file" 2>/dev/null || true)"
      if [ "$cur" != "$last" ]; then
        printf '\n== %s  %s ==\n' "$(date +%H:%M:%S)" "$file"
        "$0" lean "$file" || true
        last="$cur"
      fi
      sleep 1
    done
    ;;
  audit|audits)
    run_audits
    ;;
  full)
    "$LAKE" build
    run_audits
    run_e8p_tests
    ;;
  e8p)
    run_e8p_tests
    ;;
  build|compile)
    "$LAKE" build
    ;;
  all)
    "$LAKE" build
    run_audits
    ;;
  *)
    if [ -f "$1" ] && [[ "$1" == *.lean ]]; then
      "$LAKE" build "$1:olean"
    else
      "$LAKE" build "$@"
    fi
    ;;
esac
