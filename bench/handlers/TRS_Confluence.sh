#!/usr/bin/env bash
set -euo pipefail
. "$(dirname "$0")/../lib/solver.sh"

tmpdir="$(mktemp -d)"; trap 'rm -rf "$tmpdir"' EXIT
tmp="$tmpdir/input.ari"
mkinput "$tmp" "(GOAL CONFLUENCE)" < "$BENCHMARK"

[ "${PRINT_INPUT:-0}" = 1 ] && { printf '%s\n' "---BEGIN INPUT (TRS_Confluence)---" >&2; cat "$tmp" >&2; printf '%s\n' "---END INPUT---" >&2; }

if [ "${CERT:-false}" = true ]; then
  run_cpf_convert "$tmp"
else
  run_plain "$tmp" "" -t "${TIMEOUT}"
fi
