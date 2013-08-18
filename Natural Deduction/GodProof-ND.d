# vim: ft=make
.PHONY: GodProof-ND._graphics
GodProof-ND.aux GodProof-ND.aux.make GodProof-ND.d GodProof-ND.pdf: $(call path-norm,/usr/local/texlive/2010/texmf-dist/tex/latex/base/article.cls)
GodProof-ND.aux GodProof-ND.aux.make GodProof-ND.d GodProof-ND.pdf: $(call path-norm,/usr/local/texlive/2010/texmf-dist/tex/latex/base/latexsym.sty)
GodProof-ND.aux GodProof-ND.aux.make GodProof-ND.d GodProof-ND.pdf: $(call path-norm,/usr/local/texlive/2010/texmf-dist/tex/latex/bussproofs/bussproofs.sty)
GodProof-ND.aux GodProof-ND.aux.make GodProof-ND.d GodProof-ND.pdf: $(call path-norm,GodProof-ND.tex)
.SECONDEXPANSION:
