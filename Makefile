
coq_grep: extract
	ocamlbuild uniq.byte

extract: extraction.v Coq_uniq.vo
	coqtop -batch -load-vernac-source $<

%.vo: %.v
	coqc $<

clean:
	rm -f *.o *.cmi *.cmo *.cmx *.vo
