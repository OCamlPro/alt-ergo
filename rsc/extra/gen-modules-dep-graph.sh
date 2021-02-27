TMPDIR="."

if [ -d "/tmp/" ]; then
    TMPDIR="/tmp"
fi

cmd=""

##
printf "\033[32m=> Listing ml* files ...\e[0m\n"
for file in `find src -name '*'.ml'*'`; do
    cmd="$file $cmd"
done

##

printf "\033[32m=> Adding -I <dirs>\e[0m\n"

for dir in `find src -type d`; do
    cmd="-I $dir $cmd"
done

##

ocamldepDBG=`mktemp $TMPDIR/ocamldepdbg_XXXXX`
ocamldepRES=`mktemp $TMPDIR/ocamldepres_XXXXX`

printf "\033[32m=> Running ocamldep. Command available in tmp file $ocamldepDBG and result in $ocamldepRES\e[0m\n"

echo "ocamldep $cmd" > $ocamldepDBG
ocamldep $cmd > $ocamldepRES

##

printf "\033[32m=> Compiling ocamldot sources (make -C rsc/extra/ocamldot)\e[0m\n"
make -C rsc/extra/ocamldot

##

ocamldotRES=`mktemp $TMPDIR/ocamldotres_XXXXX`

printf "\033[32m=> Running ocamldot on content of $ocamldepRES. Result will be stored in $ocamldotRES\e[0m\n"

./rsc/extra/ocamldot/ocamldot $ocamldepRES > $ocamldotRES

##
ocamldotfullRES=`mktemp $TMPDIR/ocamldotfullres_XXXXX`

printf "\033[32m=> Concatenaing content of ./rsc/extra/subgraphs.dot. Result will be stored in $ocamldotfullRES\e[0m\n"

grep -v "}" $ocamldotRES > $ocamldotfullRES
cat ./rsc/extra/subgraphs.dot >> $ocamldotfullRES
echo "}" >> $ocamldotfullRES


## Generating PDF file modules-dep-graph.pdf with dot from $ocamldotfullRES

dot -Tpdf $ocamldotfullRES > modules-dep-graph.pdf

printf "\033[32m=> To open the generated file, try something like \e[4mevince modules-dep-graph.pdf\e[0m\n"
