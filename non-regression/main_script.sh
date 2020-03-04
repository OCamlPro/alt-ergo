rm -f main_script.log

## Given parameters
################################################################################################

pr=`pwd`/alt-ergo.opt

if [ "$pr" = "" ] ; then
    echo "`basename $0`: No prover is given!"
    exit 1
else if [ ! -f $pr ] ; then
    echo "`basename $0`: Given prover \"$pr\" not found!"
    exit 1
else if [ ! -x "$pr" ] ; then
    echo "$`basename $0`: Given prover \"$pr\" not executable!"
    exit 1
fi
fi
fi

opt=$1
echo "COMMAND: $pr $opt <file>"

## PP options
################################################################################################

cpt=0
COLS=$(tput cols)
limit=""
while [ $cpt -lt $COLS ]; do
    cpt=`expr $cpt + 1`
    limit=`echo -n $limit-`
done

echo -n "$limit"

main_script_out=$(mktemp)
main_script_err=$(mktemp)
trap "rm $main_script_out $main_script_err" EXIT

## Challenges
################################################################################################

score=0
total=0

big_total=`ls challenges/*/*.mlw | wc -l`
for kind in `ls challenges/`
do
    echo ""
    echo -n "challenges/$kind"
    for mlw in `ls challenges/$kind/*.mlw`
    do
        tput hpa 25
        total=`expr $total + 1`
        echo -n "$total / $big_total"
        timeout 2 $pr $mlw $opt 1> $main_script_out 2> $main_script_err
        if grep -q -w Valid $main_script_out ; then
	    score=`expr $score + 1`
            echo "\e[32m    > [OK] ../non-regression/$mlw\e[39m"
        else
            echo ../non-regression/$mlw >> main_script.log
            cat $main_script_out >> main_script.log
            cat $main_script_err >> main_script.log
            echo "" >> main_script.log
            echo "    > [KO] ../non-regression/$mlw"
        fi
    done
done

percent=`expr 100 \* $score / $total`
diff=`expr $total - $score`
echo ""
echo "$limit"
echo " Score Challenges: $score/$total : $percent% (-$diff) "
echo "$limit"


## Valid
################################################################################################

score=0
total=0

big_total=`ls valid/*/*.mlw | wc -l`
for kind in `ls valid/`
do
    echo ""
    echo -n "valid/$kind"
    for mlw in `ls valid/$kind/*.mlw`
    do
        tput hpa 25
        total=`expr $total + 1`
        echo -n "$total / $big_total"
        timeout 2 $pr $mlw $opt 1> $main_script_out 2> $main_script_err
        if grep -q -w Valid $main_script_out ; then
	    score=`expr $score + 1`
        else
            echo ../non-regression/$mlw >> main_script.log
            cat $main_script_out >> main_script.log
            cat $main_script_err >> main_script.log
            echo "" >> main_script.log
            echo "    > [KO] ../non-regression/$mlw"
        fi
    done
done

percent=`expr 100 \* $score / $total`
diff=`expr $total - $score`
echo ""
echo "$limit"
echo " Score Valid: $score/$total : $percent% (-$diff) "
echo "$limit"


## Invalid
################################################################################################

score=0
total=0

big_total=`ls invalid/*/*.mlw | wc -l`
for kind in `ls invalid/`
do
    echo ""
    echo -n "invalid/$kind"
    for mlw in `ls invalid/$kind/*.mlw`
    do
        tput hpa 25
        total=`expr $total + 1`
        echo -n "$total / $big_total"
        timeout 2 $pr $mlw $opt 1> $main_script_out 2> $main_script_err
        if grep -q -w "I don't know" $main_script_out ; then
	    score=`expr $score + 1`
        else
            echo ../non-regression/$mlw >> main_script.log
            cat $main_script_out >> main_script.log
            cat $main_script_err >> main_script.log
            echo "" >> main_script.log
            echo "    > [KO] ../non-regression/$mlw"
        fi
    done
done

percent=`expr 100 \* $score / $total`
diff=`expr $total - $score`
echo ""
echo "$limit"
echo " Score Invalid: $score/$total : $percent% (-$diff)"
echo "$limit"


## Incorrect
################################################################################################

score=0
total=0

big_total=`ls incorrect/*/*.mlw | wc -l`
for kind in `ls incorrect/`
do
    echo ""
    echo -n "incorrect/$kind"
    for mlw in `ls incorrect/$kind/*.mlw`
    do
        tput hpa 25
        total=`expr $total + 1`
        echo -n "$total / $big_total"
        timeout 2 $pr $mlw $opt 1> $main_script_out 2> $main_script_err
        if [ $? -eq 0 ] ; then
            echo ../non-regression/$mlw >> main_script.log
            cat $main_script_out >> main_script.log
            cat $main_script_err >> main_script.log
            echo "" >> main_script.log
            echo "    > [KO] ../non-regression/$mlw"
        else
            score=`expr $score + 1`
        fi
    done
done

percent=`expr 100 \* $score / $total`
diff=`expr $total - $score`
echo ""
echo "$limit"
echo " Score Incorrect: $score/$total : $percent% (-$diff)"
echo "$limit"
