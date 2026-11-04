#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"

LAKE="${LAKE_BIN:-lake}"

usage() {
  cat <<'USAGE'
Usage:
  ./build.sh                Build everything, run audits, run e8p checks
  ./build.sh all            Same as ./build.sh
  ./build.sh build          Build everything, no audits or e8p checks
  ./build.sh audit          Run audits only
  ./build.sh e8p            Build e8p and run its formatter/reporter checks
  ./build.sh <module>       Build one target, e.g. ./build.sh PMAction
  ./build.sh <file.lean>    Check one file, e.g. ./build.sh src/PMAction.lean
  ./build.sh help           This text

Set LAKE_BIN to use a non-default lake binary.
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
  audit|audits)
    run_audits
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
    run_e8p_tests
    ;;
  *)
    if [ -f "$1" ] && [[ "$1" == *.lean ]]; then
      "$LAKE" env lean "$@"
    else
      "$LAKE" build "$@"
    fi
    ;;
esac
