hsfiles=find . -path "./dist" -prune -o -path "./local" -prune -o -name "*.hs" -print

spellcheck:
	cat `$(hsfiles) | grep -v ./.stack-work` | tr $$'\n' ' ' | sed 's/'"'"'"'"'"'//g;s/\("[^"]*"\)/\n\1\n/g' | grep --color=never '"' > /tmp/spell
	ispell -t -d american -p dictionary.txt /tmp/spell
	echo "Differences:"
	diff /tmp/spell.bak /tmp/spell

