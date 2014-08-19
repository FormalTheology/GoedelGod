tptp4X=./tptp4X
call=./RemoteSOT.pl
# if the above programs don't work for you download the SystemOnTPTP package,
# install it and change the above paths accordingly

#proverlist='LEO-II---1.6.2 Satallax---2.7 Isabelle---2013 Nitrox---2013 agsyHOL---1.0 TPS---3.120601S1b'
proverlist='LEO-II---1.6.2 Satallax---2.7 Nitrox---2013'
#proverlist='LEO-II---1.6.2 Satallax-MaLeS---1.2 Nitrox---2013'

timeout=60

suffix=$(date "+%Y-%m-%d--%H:%M:%S")
resultsfile=RESULTS-$suffix

touch $resultsfile
rm $resultsfile

echo
echo Asking various HOL-ATPs in Miami remotely \(thanks to Geoff Sutcliffe\)
echo Asking various HOL-ATPs in Miami remotely \(thanks to Geoff Sutcliffe\) >> $resultsfile

for file in "$@"
do
echo
echo >> $resultsfile
    for prover in $proverlist 
    do
    function_to_fork () { 
      res=""
      while ! (echo $res | grep --quiet RESULT); do
          res=`$tptp4X -t $timeout -x $file | $call -t $timeout -s $prover |grep RESULT` 
	  echo ${file}---${prover}---${res}
	  echo ${file}---${prover}---${res} >> $resultsfile
      done   
    }
    function_to_fork &
    done
    wait
    echo Done 
    echo Done >> $resultsfile
done





