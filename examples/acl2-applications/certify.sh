#!/bin/sh
# Certify every book in this directory with a plain `acl2` binary
# (no cert.pl / make needed).  Usage:  ./certify.sh [book ...]
#
# For book NAME.lisp, the optional file NAME.acl2 holds forms to run
# before certification (e.g. including package definitions), and its
# line `; cert-flags: ...` gives the certify-book arguments, following
# the convention used by ACL2's build/cert.pl.
cd "$(dirname "$0")" || exit 1
ACL2=${ACL2:-acl2}
books=${*:-$(ls [0-9]*.lisp | sed 's/\.lisp$//')}
status=0
for b in $books; do
  b=${b%.lisp}
  rm -f "$b.cert"
  flags="? t"
  pre=""
  if [ -f "$b.acl2" ]; then
    pre=$(grep -v '^;' "$b.acl2")
    f=$(sed -n 's/^; cert-flags: *//p' "$b.acl2")
    [ -n "$f" ] && flags=$f
  fi
  start=$(date +%s)
  printf '%s\n(certify-book "%s" %s)\n' "$pre" "$b" "$flags" \
    | "$ACL2" > "$b.out" 2>&1
  t=$(( $(date +%s) - start ))
  if [ -f "$b.cert" ]; then
    echo "ok    $b  (${t}s)"
  else
    echo "FAIL  $b  (see $b.out)"; status=1
  fi
done
exit $status
