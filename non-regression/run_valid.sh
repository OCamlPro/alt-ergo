alt_ergo_bin=$1
timelimit=$2

files=""
files="$files `find valid/ -name '*'.mlw`"
files="$files `find valid/ -name '*'.why`"
files="$files `find valid/ -name '*'.zip`"

cpt=0
for f in $files
do
    cpt=`expr $cpt + 1`
    res=`$alt_ergo_bin -timelimit $timelimit $f`
    if [ "`echo $res | grep -c ":Valid"`" -eq "0" ]
    then
        echo "[run_valid > default test] issue with file $f"
        echo "Result is $res"
        exit 1
    fi
done
echo "[run_valid > default test] $cpt files considered"

cpt=0
for f in $files
do
    cpt=`expr $cpt + 1`
    res=`$alt_ergo_bin -timelimit $timelimit -sat-plugin satML-plugin.cmxs $f`
    if [ "`echo $res | grep -c ":Valid"`" -eq "0" ]
    then
        echo "[run_valid > satML-plugin test] issue with file $f"
        echo "Result is $res"
        exit 1
    fi
done
echo "[run_valid > satML-plugin test] $cpt files considered"

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
