#!/usr/bin/env bash
set -euo pipefail
if [ "$#" -ne 1 ]; then
  echo "Usage: $0 <iptables-save file>" >&2
  exit 1
fi
input_file="$1"
if [ ! -f "$input_file" ]; then
  echo "File not found: $input_file" >&2
  exit 1
fi
payload=$(cat "$input_file")
exec dafny run src/IptablesToSmt.dfy -- "$payload"
