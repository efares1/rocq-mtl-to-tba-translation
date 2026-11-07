#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
version_line="$(ltl2tgba --version | sed -n '1p')"
case "$version_line" in
  *"(spot) 2.16"*) ;;
  *)
    printf 'Expected Spot 2.16; found: %s\n' "$version_line" >&2
    exit 2
    ;;
esac

formula="$(<"$script_dir/worked_translation.ltl")"
ltl2tgba --buchi -S --dot=1 -f "$formula" > "$script_dir/worked_translation.dot"
printf 'Regenerated %s with %s\n' "$script_dir/worked_translation.dot" "$version_line"

alarm_formula="$(<"$script_dir/alarm_response_backend.ltl")"
ltl2tgba --buchi -S --dot=1 -f "$alarm_formula" > "$script_dir/alarm_response_backend.dot"
printf 'Regenerated %s with %s\n' "$script_dir/alarm_response_backend.dot" "$version_line"
