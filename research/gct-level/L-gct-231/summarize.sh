cd /tmp/claude-0/-home-user-pequalnp-proofs/50ee7c56-5722-5f91-8050-499f68e2afc3/scratchpad/L-gct-231/runs4
for f in ${1:-*}.log; do [ -f "$f" ] || continue; printf "%-34s runs=%-5s solved=%-4s best=%s\n" "${f%.log}" "$(grep -c normres $f)" "$(grep normres $f | awk '$3<1e-8' | wc -l)" "$(grep normres $f | sort -g -k3 | head -1 | awk '{print $3}')"; done
