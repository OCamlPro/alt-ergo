alt_ergo_bin=$1
timelimit=$2

files=""
files="$files `find valid/ -name '*'.mlw`"
files="$files `find valid/ -name '*'.why`"
files="$files `find valid/ -name '*'.zip`"

## run Alt-Ergo with imperative SAT solver assisted with tableaux on valid tests
for options in "" "--no-minimal-bj" "--no-tableaux-cdcl-in-theories" "--no-tableaux-cdcl-in-instantiation"  "--no-tableaux-cdcl-in-theories --no-tableaux-cdcl-in-instantiation" "--no-minimal-bj --no-tableaux-cdcl-in-theories --no-tableaux-cdcl-in-instantiation"
do
    cpt=0
    for f in $files
    do
        cpt=`expr $cpt + 1`
        res=`$alt_ergo_bin --timelimit $timelimit $options --sat-solver CDCL-Tableaux $f`
        if [ "`echo $res | grep -c ":Valid"`" -eq "0" ]
        then
            echo "[run_valid > default cdcl solver with tableaux] issue with file $f"
            echo "Result is $res"
            exit 1
        fi
    done
    echo "[run_valid > default cdcl solver with tableaux and options '$options'] $cpt files considered"
done

## run Alt-Ergo with functional SAT solver on valid tests
cpt=0
for f in $files
do
    cpt=`expr $cpt + 1`
    res=`$alt_ergo_bin --timelimit $timelimit --sat-solver Tableaux $f`
    if [ "`echo $res | grep -c ":Valid"`" -eq "0" ]
    then
        echo "[run_valid > tableaux solver] issue with file $f"
        echo "Result is $res"
        exit 1
    fi
done
echo "[run_valid > tableaux solver test] $cpt files considered"

## run Alt-Ergo with functional SAT solver assisted with cdcl on valid tests
cpt=0
for f in $files
do
    cpt=`expr $cpt + 1`
    res=`$alt_ergo_bin --timelimit $timelimit --sat-solver Tableaux-CDCL $f`
    if [ "`echo $res | grep -c ":Valid"`" -eq "0" ]
    then
        echo "[run_valid > tableaux solver with cdcl] issue with file $f"
        echo "Result is $res"
        exit 1
    fi
done
echo "[run_valid > tableaux solver with cdcl test] $cpt files considered"

## run Alt-Ergo with imperative SAT solver on valid tests
for options in "" "--no-minimal-bj"
do
    cpt=0
    for f in $files
    do
        cpt=`expr $cpt + 1`
        res=`$alt_ergo_bin --timelimit $timelimit $options --sat-solver CDCL $f`
        if [ "`echo $res | grep -c ":Valid"`" -eq "0" ]
        then
            echo "[run_valid > cdcl solver] issue with file $f"
            echo "Result is $res"
            exit 1
        fi
    done
    echo "[run_valid > cdcl solver with options '$options'] $cpt files considered"
done

## run Alt-Ergo with FM-Simplex on valid tests
# cpt=0
# for f in $files
# do
#     cpt=`expr $cpt + 1`
#     res=`$alt_ergo_bin -timelimit $timelimit -inequalities-plugin fm-simplex-plugin.cmxs $f`
#     if [ "`echo $res | grep -c ":Valid"`" -eq "0" ]
#     then
#         echo "[run_valid > fm-simplex-plugin test] issue with file $f"
#         echo "Result is $res"
#         exit 1
#     fi
# done
# echo "[run_valid > fm-simplex-plugin test] $cpt files considered"


## run Alt-Ergo with imperative SAT solver and FM-Simplex on valid tests
# cpt=0
# for f in $files
# do
#     cpt=`expr $cpt + 1`
#     res=`$alt_ergo_bin -timelimit $timelimit -sat-plugin satML-plugin.cmxs -inequalities-plugin fm-simplex-plugin.cmxs $f`
#     if [ "`echo $res | grep -c ":Valid"`" -eq "0" ]
#     then
#         echo "[run_valid > satML-plugin+fm-simplex-plugin test] issue with file $f"
#         echo "Result is $res"
#         exit 1
#     fi
# done
# echo "[run_valid > satML-plugin+fm-simplex-plugin test] $cpt files considered"


# TODO: test save-used / replay-used context

# TODO: test proofs replay ?
