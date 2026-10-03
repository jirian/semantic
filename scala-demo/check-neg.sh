#!/usr/bin/env bash
# Each file in neg/ must be rejected by the separation checker.
set -u
cd "$(dirname "$0")"
status=0
for f in neg/*.scala; do
  cp "$f" src/main/scala/Neg.scala
  out=$(sbt -batch compile 2>&1)
  rm -f src/main/scala/Neg.scala
  if echo "$out" | grep -q "Compilation failed"; then
    echo "REJECTED (as expected): $f"
    echo "$out" | grep -E "^\[error\] +\|" | grep -iv "^\[error\] +\| *\^" | head -3 | sed 's/^/    /'
  else
    echo "ACCEPTED (unexpected!): $f"; status=1
  fi
done
exit $status
