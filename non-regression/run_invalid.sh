alt_ergo_bin=$1
timelimit=$2

files=""
files="$files `find invalid/ -name '*'.mlw`"
files="$files `find invalid/ -name '*'.why`"
files="$files `find invalid/ -name '*'.zip`"


## run Alt-Ergo with functional SAT solver on invalid tests
cpt=0
for f in $files
do
    cpt=`expr $cpt + 1`
    res=`$alt_ergo_bin -timelimit $timelimit $f`
    if [ "`echo $res | grep -c ":I don't know"`" -eq "0" ]
    then
        echo "[run_invalid > default test] issue with file $f"
        echo "Result is $res"
        exit 1
    fi
done
echo "[run_invalid > default test] $cpt files considered"


## run Alt-Ergo with imperative SAT solver on invalid tests
for options in "" "-minimal-bj" "-lazy-sat" "-minimal-bj -lazy-sat"
do
    cpt=0
    for f in $files
    do
        cpt=`expr $cpt + 1`
        res=`$alt_ergo_bin -timelimit $timelimit -sat-plugin satML-plugin.cmxs $f`
        if [ "`echo $res | grep -c ":I don't know"`" -eq "0" ]
        then
            echo "[run_invalid > satML-plugin test] issue with file $f"
            echo "Result is $res"
            exit 1
        fi
    done
    echo "[run_invalid > satML-plugin test with options '$options'] $cpt files considered"
done


## run Alt-Ergo with FM-Simplex on invalid tests
cpt=0
for f in $files
do
    cpt=`expr $cpt + 1`
    res=`$alt_ergo_bin -timelimit $timelimit -inequalities-plugin fm-simplex-plugin.cmxs $f`
    if [ "`echo $res | grep -c ":I don't know"`" -eq "0" ]
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
    res=`$alt_ergo_bin -timelimit $timelimit -sat-plugin satML-plugin.cmxs -inequalities-plugin fm-simplex-plugin.cmxs $f`
    if [ "`echo $res | grep -c ":I don't know"`" -eq "0" ]
    then
        echo "[run_invalid > satML-plugin+fm-simplex-plugin test] issue with file $f"
        echo "Result is $res"
        exit 1
    fi
done
echo "[run_invalid > satML-plugin+fm-simplex-plugin test] $cpt files considered"

# TODO: test save-used / replay-used context

# TODO: test proofs replay ?
