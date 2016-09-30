proverlist='leo satallax'
queue=$1
timeout=$2
shift
shift
filelist=$@

vsc="qsub -q ${queue}.q"

echo
echo Generating and scheduling jobs at VSC
echo

for file in $filelist
do
    for prover in $proverlist 
    do
    	jobname="$file-$prover"
    	jobfile="${jobname}.job"
    	function_to_fork () { 
            echo -e "#\$ -N $jobname" >> $jobfile  # declares job name               
	    echo -e "#\$ -pe mpich 16" >> $jobfile # requests 16 cores
	    echo -e "#\$ -V" >> $jobfile # imports all environment variables
            echo -e "#\$ -M bruno.wp@gmail.com" >> $jobfile # email address to be notified
            echo -e "#\$ -m beas" >> $jobfile # notifies of beginning, end, abortion and rescheduling of job
	    echo -e "#\$ -l h_rt=$(($timeout + 600))\n" >> $jobfile # runs job for a maximum time of hh:mm:ss

            echo -e "$prover -t $timeout $file" >> $jobfile
 
            echo "scheduling $prover on $file"
            $vsc $jobfile 
    	}
    	function_to_fork &
    done
    echo 
done


