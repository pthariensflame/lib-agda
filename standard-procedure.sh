source ~/.bash_profile

find . -name "*.agdai" -print0 | xargs -0 rm -rfv
rm -rfv Everything.agda html dep-graph*

./dist/build/GenerateEverything/GenerateEverything
if [ -a Everything.agda ]; then
  agda --html --dependency-graph=dep-graph.dot -i . -i src README.agda
  if [ -a dep-graph.dot ]; then
    cat dep-graph.dot | tred | dot -Tpdf > dep-graph.pdf
  fi
fi
