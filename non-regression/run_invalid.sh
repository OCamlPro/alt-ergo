alt_ergo_bin=$1
timelimit=$2
simple_test=$3

files=""
files="$files `find invalid/ -name '*'.ae`"
files="$files `find invalid/ -name '*'.zip`"

## Test sat options if simple_test is not set
if $simple_test
then
    min_bj="--no-minimal-bj"
    tab_th="--no-tableaux-cdcl-in-theories"
    tab_inst="--no-tableaux-cdcl-in-instantiation"
    tab_th_inst="--no-tableaux-cdcl-in-theories --no-tableaux-cdcl-in-instantiation"
    min_bj_tab_th_inst="--no-minimal-bj --no-tableaux-cdcl-in-theories --no-tableaux-cdcl-in-instantiation"
fi

## run Alt-Ergo with imperative SAT solver assisted with tableaux on invalid tests
for options in "" $min_bj $tab_th $tab_inst $tab_th_inst $min_bj_tab_th_inst
do
    cpt=0
    for f in $files
    do
        cpt=`expr $cpt + 1`
        res=`$alt_ergo_bin --timelimit $timelimit $options --sat-solver CDCL-Tableaux $f`
        if [ "`echo $res | grep -c "I don't know"`" -eq "0" ]
        then
            echo "[run_invalid > default cdcl solver with tableaux] issue with file $f"
            echo "Result is $res"
            exit 1
        fi
    done
    echo "[run_invalid > default cdcl solver with tableaux and options '$options'] $cpt files considered"
done

## run Alt-Ergo with functional SAT solver on invalid tests
cpt=0
for f in $files
do
    cpt=`expr $cpt + 1`
    res=`$alt_ergo_bin --timelimit $timelimit --sat-solver Tableaux $f`
    if [ "`echo $res | grep -c "I don't know"`" -eq "0" ]
    then
        echo "[run_invalid > tableaux solver] issue with file $f"
        echo "Result is $res"
        exit 1
    fi
done
echo "[run_invalid > tableaux solver test] $cpt files considered"

## run Alt-Ergo with functional SAT solver assisted with cdcl on invalid tests
cpt=0
for f in $files
do
    cpt=`expr $cpt + 1`
    res=`$alt_ergo_bin --timelimit $timelimit --sat-solver Tableaux-CDCL $f`
    if [ "`echo $res | grep -c "I don't know"`" -eq "0" ]
    then
        echo "[run_invalid > tableaux solver with cdcl] issue with file $f"
        echo "Result is $res"
        exit 1
    fi
done
echo "[run_invalid > tableaux solver with cdcl test] $cpt files considered"

## run Alt-Ergo with imperative SAT solver on invalid tests
for options in "" $min_bj
do
    cpt=0
    for f in $files
    do
        cpt=`expr $cpt + 1`
        res=`$alt_ergo_bin --timelimit $timelimit $options --sat-solver CDCL $f`
        if [ "`echo $res | grep -c "I don't know"`" -eq "0" ]
        then
            echo "[run_invalid > cdcl solver] issue with file $f"
            echo "Result is $res"
            exit 1
        fi
    done
    echo "[run_invalid > cdcl solver with options '$options'] $cpt files considered"
done

## run Alt-Ergo with FM-Simplex on invalid tests
cpt=0
for f in $files
do
    cpt=`expr $cpt + 1`
    res=`$alt_ergo_bin --timelimit $timelimit --inequalities-plugin fm-simplex-plugin.cmxs $f`
    if [ "`echo $res | grep -c "I don't know"`" -eq "0" ]
    then
        echo "[run_invalid > fm-simplex-plugin test] issue with file $f"
        echo "Result is $res"
        exit 1
    fi
done
echo "[run_invalid > fm-simplex-plugin test] $cpt files considered"


## run Alt-Ergo with imperative SAT solver and FM-Simplex on invalid tests
cpt=0
for f in $files
do
    cpt=`expr $cpt + 1`
    res=`$alt_ergo_bin --timelimit $timelimit --sat-plugin satML-plugin.cmxs --inequalities-plugin fm-simplex-plugin.cmxs $f`
    if [ "`echo $res | grep -c "I don't know"`" -eq "0" ]
    then
        echo "[run_invalid > satML-plugin+fm-simplex-plugin test] issue with file $f"
        echo "Result is $res"
        exit 1
    fi
done
echo "[run_invalid > satML-plugin+fm-simplex-plugin test] $cpt files considered"

# TODO: test save-used / replay-used context

# TODO: test proofs replay ?
