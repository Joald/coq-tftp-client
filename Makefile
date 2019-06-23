
coq_grep: extract
	ocamlbuild -I coq -pkg unix main.byte

extract: extraction.v client.vo
	coqtop -batch -load-vernac-source $<

%.vo: %.v
	coqc $<

clean:
	rm -f *.o *.cmi *.cmo *.cmx *.vo
