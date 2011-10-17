AGDA=Exercises
PDF=AgdaExercises01

all:
	lhs2TeX --agda $(AGDA).lagda >$(PDF).tex && pdflatex $(PDF).tex && evince $(PDF).pdf
