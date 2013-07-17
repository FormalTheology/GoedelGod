tptp4X=./tptp4X
call=./RemoteSOT.pl
# if the above programs don't work for you download the SystemOnTPTP package,
# install it and change the above paths accordingly

proverlist='LEO-II---1.6.0 Satallax---2.7 Isabelle---2013 Nitrox---2013 agsyHOL---1.0 cocATP---0.1.8'
timeout=20

echo
echo Asking various HOL-ATPs in Miami remotely \(thanks to Geoff Sutcliffe\)
echo

for file in "$@"
do
    for prover in $proverlist 
    do
    function_to_fork () { 
        echo $prover : $file ++++++ `$tptp4X -t $timeout -x $file | $call -t $timeout -s $prover -q01`
    }
    function_to_fork &
    done
    echo 
done





