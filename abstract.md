title:
	All You Need Is Refl --- Almost
subtitle:
    Return of the Renamings

authors:
	Peter Thiemann, Marius Weidner

abstract:
	In 2024, Philip Wadler proposed *Explicit Weakening*, a novel formulation of substitution
	in which many facts about substitution can be proved by reflexivity in a proof assistant
	such as Agda. The approach dispenses with renamings by making weakening explicit in the syntax.

	We pick up where Wadler left off. We discuss the limitations of explicit weakening and propose
	an alternative that revives renamings while retaining its main advantage for mechanized proofs.
	Our approach uses rewriting type theory with a confluent selection of equations from the
	σ-calculus with first-class renamings. We validate the approach on substantial System F
	developments, including canonicity and logical-relations proofs.
