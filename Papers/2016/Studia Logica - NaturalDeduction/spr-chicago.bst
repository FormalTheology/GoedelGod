%% This is file `spr-chicago.bst'
%%
%% Please submit bugs or your comments to vtex@vtex.lt
%%
%% You are free to use this style file as you see fit, provided 
%% that you do not make changes to the file. 
%% If you DO make changes, you are required to rename this file.
%%
%% It may be distributed under the terms of the LaTeX Project Public
%% License, as described in lppl.txt in the base LaTeX distribution.
%% Either version 1.0 or, at your option, any later version.

% BibTeX programming: Linas Stonys, VTeX, Lithuania, lstonys@vtex.lt 
%


ENTRY
  { address
    author
    booktitle
    chapter
    doi
    edition
    fjournal
    editor
    howpublished
    institution
    isbn
    journal
    key
    month
    note
    number
    organization
    pages   
    publisher
    school
    series
    title
    type
    volume
    year
    url
    info
    options
  }
  {}
   { label extra.label sort.label short.list }

INTEGERS { output.state before.all mid.sentence after.sentence
           after.block after.authors between.elements bother slen set.settings default.info middle.edt}

FUNCTION {init.state.consts}
{ #0 'before.all :=
  #1 'mid.sentence :=
  #2 'after.sentence :=
  #3 'after.block :=
  #4 'after.authors :=
  #5 'between.elements :=
}

STRINGS { s t  element}
STRINGS { longest.label last.label list.string}
STRINGS { v l f j b }

FUNCTION {output.nonnull}
{ 's :=
  output.state mid.sentence =
    { " " * write$ newline$}
    { output.state after.block =
        { add.period$ write$
          newline$
         % "\newblock " write$
        }
        {
          output.state after.authors =
          { ". " * write$
            newline$
          }
          { output.state between.elements =
              { ", " * write$ newline$}
              { output.state before.all =
                   'write$
                  { add.period$ " " * write$ newline$}
                  	
                  	
                  if$
              }
              if$
          }
          if$
        }
      if$
      mid.sentence 'output.state :=
    }
  if$
  s
}

FUNCTION {output}
{ duplicate$ empty$
    'pop$
    'output.nonnull
  if$
}

FUNCTION {output.check}
{ 't :=
  duplicate$ empty$
    { pop$ "empty " t * " in " * cite$ * warning$ }
    'output.nonnull
  if$
}

FUNCTION {stupid.colon}
{ after.authors 'output.state := }


FUNCTION {insert.comma}
{ output.state before.all =
    'skip$
    { between.elements 'output.state := }
  if$
}

FUNCTION {new.sentence}
{ output.state after.block =
    'skip$
    { output.state before.all =
        'skip$
        { after.sentence 'output.state := }
      if$
    }
  if$
}

FUNCTION {not}
{   { #0 }
    { #1 }
  if$
}

FUNCTION {and}
{   'skip$
    { pop$ #0 }
  if$
}

FUNCTION {or}
{   { pop$ #1 }
    'skip$
  if$
}
INTEGERS {sk}

FUNCTION {field.or.null}
{ duplicate$ empty$
    { pop$ "" }
    'skip$
  if$
}

FUNCTION {sort.format.month}
{ 't :=
 	 t #1 #2 substring$ "01" =
 	 t	#1 #1 substring$ "1" =
 	 t	#2 #2 substring$ "" =
 	 and or
 	 { "January" }
    { t #1 #2 substring$ "02" =
			t	#1 #1 substring$ "2" =
			t	#2 #2 substring$ "" =
			and or
      { "February" }
      { t #1 #2 substring$ "03" =
 		    t #1 #1 substring$ "3" =
 		    t	#2 #2 substring$ "" =
 		    and or
        { "March" }
        { t #1 #2 substring$ "04" =
        	t #1 #1 substring$ "4" =
        	or
          { "April" }
          { t #1 #2 substring$ "05" =
           	t #1 #1 substring$ "5" =
           	or
            { "May" }
            { t #1 #2 substring$ "06" =
  	          t #1 #1 substring$ "6" =
  	          or
              { "June" }
              { t #1 #2 substring$ "07" =
              	t #1 #1 substring$ "7" =
              	or
                { "July" }
                { t #1 #2 substring$ "08" =
 		              t #1 #1 substring$ "8" =
 		              or
                  { "August" }
                  { t #1 #2 substring$ "09" =
                    t #1 #1 substring$ "9" =
                    or
                    { "September" }
                    { t #1 #2 substring$ "10" =
                      { "October" }
                      { t #1 #2 substring$ "11" =
                        { "November" }
                        { t #1 #2 substring$ "12" =
                          { "December" }
                          { t } % No match
                        if$
                        }
                      if$
                      }
                    if$
                    }
                  if$
                  }
                if$
                }
              if$
              }
            if$
            }
          if$
          }
        if$
        }
      if$
      }
    if$
    }
  if$
 
}

FUNCTION {is.num}
{ chr.to.int$
  duplicate$ "0" chr.to.int$ < not
  swap$ "9" chr.to.int$ > not and
}

FUNCTION {byear}
{ duplicate$ empty$
    { pop$ "" }
    {	't :=
    	
    	#0 bother =
			{""}
		    { "\byear{" }
		if$	
    	
    	t text.length$ 'sk :=
		#5 sk =
			{t #1 #4 substring$ 's :=
			 t #5 #1 substring$ 'longest.label :=
		  	 longest.label is.num not	
				{ s * 
	    		  #0 bother =
					'skip$
			    	{ "}" *}
				  if$	
				  longest.label * }
				{ 
				  t * 
	    		  #0 bother =
					'skip$
			    	{ "}" *}
				  if$	
				}
			 if$
			}
			{ t * 
    		  #0 bother =
				'skip$
		    	{ "}" *}
			  if$	
				 
			 extra.label *
			}
		if$
    }
  if$
}

FUNCTION {bissue}
{ duplicate$ empty$
    { pop$ "" }
    { #0 bother =
				'skip$
		    { "\bissue{" swap$ * "}" * }
			if$	
  	}
  if$
}

FUNCTION {binstitute}
{ duplicate$ empty$
    { pop$ "" }
    { #0 bother =
				'skip$
		    { "\binstitute{" swap$ * "}" * }
			if$	
  	}
  if$
}
FUNCTION {bsnm}
{ duplicate$ empty$
    { pop$ "" }
    { "\bsnm{" swap$ * "}" * }
  if$
}
FUNCTION {bpublisher}
{ duplicate$ empty$
    { pop$ "" }
    { #0 bother =
    		 'skip$
    		 {"\bpublisher{" swap$ * "}" * }
    	if$
    }
  if$
}
FUNCTION {bfpage}
{ duplicate$ empty$
    { pop$ "" }
    { #0 bother =
    		 'skip$
		     { "\bfpage{" swap$ * "}" * }
    	if$
    }
  if$
}
FUNCTION {blpage}
{ duplicate$ empty$
    { pop$ "" }
    { #0 bother =
    		 'skip$
		     { "\blpage{" swap$ * "}" * }
    	if$
    }
  if$
}
FUNCTION {bvolume}
{ duplicate$ empty$
    { pop$ "" }
    { #0 bother =
		    'skip$ %{ "\textbf{" swap$ * "}" * }
		    { "\bvolume{" swap$ * "}" * }
    	if$
    }
  if$
}
FUNCTION {betal}
{ duplicate$ empty$
    { pop$ "" }
    { "\betal{" swap$ * "}" * }
  if$
}
FUNCTION {binits}
{ duplicate$ empty$
    { pop$ "" }
    { "\binits{" swap$ * "}" * }
  if$
}
FUNCTION {bseriesno}
{ duplicate$ empty$
    { pop$ "" }
    { #0 bother =
		    'skip$%{ "\textbf{" swap$ * "}" * }
    		{ "\bseriesno{" swap$ * "}" * }
		if$	
  	}
  if$
}
FUNCTION {bbtitle}
{ duplicate$ empty$
    { pop$ "" }
    { #0 bother =
    		{"\textit{" swap$ * "}" *}
    		{"\bbtitle{" swap$ * "}" *}
		if$	
  	}
  if$
}


FUNCTION {bparticle}
{ duplicate$ empty$
    { pop$ "" }
    { "\bparticle{" swap$ * "}" * }
  if$
}
FUNCTION {bsuffix}
{ duplicate$ empty$
    { pop$ "" }
    { " \bsuffix{" swap$ * "}" * }
  if$
}
FUNCTION {blocation}
{ duplicate$ empty$
    { pop$ "" }
    { #0 bother =
			'skip$
		    {        	
		    	type$ "inproceedings" =
		    	publisher empty$ 
        		and
        			{"\bconflocation{"}
        			{"\blocation{"}
		 		if$	
			    swap$ * "}" * 
		    }
		if$	
  	}
  if$
}


FUNCTION {bjtitle}
{ duplicate$ empty$
    { pop$ "" }
    { #0 bother =
		    { "\textit{" }
		    { "\bjtitle{" }
		if$	
		swap$ * "}" * 
  	}
  if$
}
FUNCTION {batitle}
{ duplicate$ empty$
    { pop$ "" }
    { #0 bother =
		    'skip$
		    { "\batitle{" swap$ * "}" *}
			if$	
  	}
  if$
}
FUNCTION {bctitle}
{ duplicate$ empty$
    { pop$ "" }
    { #0 bother =
		'skip$
    	{"\bctitle{" swap$ * "}" *}
	  if$	
  	}
  if$
}

FUNCTION {springer.publisher}
{publisher #1 #8 substring$ "Springer" =
	{ "Springer"  }
  { publisher }
if$
}
FUNCTION {format.date}
{ year empty$
    { "" }
    { year byear }
  if$
}
FUNCTION {fformat.date}
{ year empty$
    'skip$
    { year byear output}
  if$
}

FUNCTION {f.date}
{ year empty$
    'skip$
    { ", "  year  byear }
  if$
}

FUNCTION {format.pub.address}
{ 
    address empty$
   		{""}
   		{address blocation}
   	if$
   	
   	address empty$ publisher empty$ or
		'skip$
		{":" *}
	if$
	output

	publisher empty$
    	{organization empty$
    		'skip$
	    	{ author empty$ editor empty$ and
    			'skip$
    			{new.sentence organization binstitute output}
    		if$
    		}
    	if$	
    	
    	type$ "booklet" = 
    		{
		     howpublished empty$
    				'skip$
    				{new.sentence howpublished bpublisher output }
   			 if$
    		}	
    		{
		     howpublished empty$
    				'skip$
    				{new.sentence howpublished binstitute output }
   			 if$
    		}
    	if$		
    	}
    	{
         springer.publisher bpublisher  output
        }
    if$
   		    
}


INTEGERS { nameptr namesleft numnames}

FUNCTION {space.after.dot}
{'j :=
	t 'f :=
	j 't := 
	s 'j :=
	"" 'l :=
	"" 's :=
%"orig=" t * top$
  { t empty$ not }
  {   
    t #1 #3 substring$ "{-}" =
	     {l  " {q}. " * 'l :=
	  	  t #4 global.max$ substring$ 't :=
	     }
   		 'skip$ 	
    if$

  	t #1 #1 substring$ 's :=
		  l  s * 'l := 

      s "." = 
		{ 

    	  	t #2 #1 substring$ " " =
    	      'skip$
		 	  {
		  	   l  " " * 'l := 
			   t #2 #4 substring$ "{\,}" =
		 	  		{
				  	  t #5 global.max$ substring$ 't :=
		 	  		}
    	     	  'skip$
      	  	   if$ 
		      } 
      	  	if$  
		} 
		'skip$
      if$

  	  t #2 global.max$ substring$ 't :=
    }
  while$
  f 't :=
  j 's :=
  l 
%"new="  l * top$ 
}

FUNCTION {format.author.editor}
{ 'b :=
   	b "editor"  =
   	b "beditor" =
   	b "neditor" =
   	or or
		{editor 's :=}
		{author 's :=}
	if$
 	%% apdoroju varda
   s space.after.dot 's :=

   "" 't :=	
	", " 'longest.label := 
  #1 'nameptr :=
  s num.names$ 'numnames :=
  numnames 'namesleft :=
    { namesleft #0 > }
    {
		b "neditor" =
			{
    		s nameptr "{vv~}"   format.name$ 'v := 
        	s nameptr "{ll}"    format.name$ 'l :=   
    		s nameptr "{ff}"    format.name$ 'f := 
     		s nameptr "{jj}"    format.name$ 'j := 
			}
			{
    		s nameptr "{vv~}"   format.name$ bparticle 'v := 
        	s nameptr "{ll}"    format.name$ bsnm 'l :=   
    		s nameptr "{ff}"    format.name$ binits  'f := 
     		s nameptr "{jj}"    format.name$ bsuffix 'j := 
			}
		if$
  		l  "\bsnm{others}" =
   		l  "\bsnm{{others}}" =
   		l  "\bsnm{et al}" =
   		l  "\bsnm{{et al}}" =
   		or or or
   		{	b "bauthor" =
   		 	b "beditor" =
		   	or
		   		 {"et al"  * }
   				 {"\betal"  * }
				if$
  		}
   		{
		   	j empty$
				   {"" 'j :=} 		
			     'skip$
				if$

		   	f empty$
				   {"" 'longest.label :=} 		
			     'skip$
				if$

   			b "editor" =
	 			{"\beditor{"}
		  		'skip$
			if$

   			b "author" =
	 			{"\bauthor{"}
		  		'skip$
			if$

   			b "bauthor" =
   			b "beditor" =
   			or
	  			{"\oauthor{"}
	  			'skip$
			if$

   			b "neditor" =
   				{""}
	  			'skip$
			if$
			
			nameptr #1 =
			middle.edt #1 = not
			and
				{* v * l * j * longest.label * f }
				{* f * " " * v * l * j }
			if$
			
			* 
			
   			b "neditor" =
   				{""}
				{"}"}  
			if$
			
			* "" 't :=
		 } 
		if$

	 	namesleft #0 >
        { namesleft #1 >
            { namesleft #2 =
    		        	{ s numnames "{ll}" format.name$ "others" =
    		        	  	{", " * t * }
    		        	  	{ 
    		        	  		numnames #2   =
   								middle.edt #1 =
   								and
    		        	    		{" and "} 
    		        	    		{", and "}
    		        	    	if$ 
    		        	  		* t * 
    		        	  	}
    		        	  if$
    		        	}
    		        	{", " * t * }
		          if$
           	}
            {""}
          if$
        }
        't      
      if$

      nameptr #1 + 'nameptr := 
      namesleft #1 - 'namesleft :=
    }
  while$  

}

FUNCTION {prepare.editors}
{   bother #0 =
		{author empty$
   		  	{"beditor"}
   			{"neditor"}
   		 if$
  		}
		{"editor"}
	if$  
	format.author.editor
}

FUNCTION {format.editors}
{ editor empty$
    { "" }
    { 
		prepare.editors
	    author empty$
    		{
	    	  editor num.names$ #1 >
    	    	{ ", eds"}
	       		{ ", ed" }
    		 if$
    		 *
    		}
	    	'skip$
   		if$	
		        
    }
  if$
  
}

FUNCTION {format.middle.editors}
{ editor empty$
    'skip$
    { #1 'middle.edt :=
      	editor num.names$ #1 >
	    	{ "eds. "}
   			{ "ed. " }
		if$
		prepare.editors
		*
	  output
	  #0 'middle.edt :=
    }
  if$
}

FUNCTION {format.authors}
{ author empty$
    	{ "" }
 		{ 	bother #0 =
				{"bauthor"}
 				{"author"}
 			if$
 			format.author.editor
 		}
  if$
}


FUNCTION {cite.author.editor}
{ 's :=
  s #1 "{vv~}{ll}" format.name$
  s num.names$ 
  #2 >
    {  " et~al." * }
    {s num.names$ #2 =
    	  { s #2 "{vv~}{ll}{ jj}{ f}" format.name$ "others" =
      			{ " et~al."  * }
     				{ " and "  s #2 "{vv~}{ll}" format.name$ * *}
     			if$
     		}
     		'skip$
     if$
    }
  if$
}

FUNCTION {check.auth.edit.org}
{author empty$
		{
			editor empty$
					{
						organization empty$
								{""}
								{organization}
						if$		
					}
					{editor cite.author.editor}
			if$		
		}
		{author cite.author.editor}
 if$	
}


FUNCTION {check.year}
{year empty$
		{""}
		{year extra.label *
		}
	if$	
}

INTEGERS { multiresult char.num k int}
INTEGERS {str.length count return save.num1 save.num2}
FUNCTION {is.in.list}{
	'f :=
	%%%% issisaugoju originalius "s" ir "t"
	s 'j :=
	f 's :=
	t 'f :=  
  list.string text.length$ 'str.length :=
  list.string 't :=
%  s text.length$ 'slen :=
  int   'save.num1 :=
  count 'save.num2 :=
  #1 'int :=
  #1 'count :=
  #0 'return :=
    
    { count str.length = not 
      #0 str.length = not
      and
    }
    {
			count #1 + 'count :=
		  t int #1 substring$ "," =
      	{
      	  t #1 int substring$ s "," * =
      	    {
		  		   #1 'return :=
  			      str.length 'count :=
			   	  }
	    			'skip$
         if$
	        
	        int #1 + 'int :=
   		    t int global.max$ substring$ 't :=
				  #0 'int :=
      	}
      	'skip$
      if$	
      int #1 + 'int :=
%			"count=" count int.to.str$ * " slen=" * str.length int.to.str$ * top$
    }
  while$

  save.num1 'int   :=
  save.num2 'count :=
  
  #0 return =
  	{ s t =
		    {#1 'return :=}
		    'skip$
		  if$
  	}
  	'skip$
  if$
	%%%% grazinu originalius "s" ir "t"
	j 's :=
	f 't :=  
	
	return		
}


FUNCTION {output.bibitem}
{ newline$
  "\bibitem"
  "nameyear" is.in.list
     {
 	    "[\protect\citeauthoryear{" * write$
	   			check.auth.edit.org write$ 
	   	"}{" write$ 
	   			check.year write$ 
	   	"}]" 
    }
    'skip$
  if$
  "alpha" is.in.list
     {
 	    "[" * write$
  	  label write$
	    "]" 
    }
    'skip$
  if$

  "{" * write$  
  cite$ write$
  "}" write$

  newline$
  "" before.all 'output.state :=
}

FUNCTION {string.to.integer}
{ 't :=
    t text.length$ 'k :=
  #1 'char.num :=
      { t char.num #1 substring$ 's :=
	 	  s is.num
	 	  s "." =
	 	  or 
	 	  char.num k = not
	 	  and
	 	 	}
	 	 {char.num #1 + 'char.num :=}
  while$
%  char.num #1 - 'char.num :=
  t #1 char.num substring$ 
  
%  "S" k * write$
}
FUNCTION {check.chapter}
{ #0 'char.num :=
      chapter text.length$ #10 >
				  {#1 'char.num :=}
				  'skip$
			if$
		char.num
}

 
FUNCTION {find.integer}
{ 't :=
  #0 'int :=
    { int not
      t empty$ not
      and
    }
    { t #1 #1 substring$ 's :=
    	s is.num 
        {#1 'int :=}
        { t #2 global.max$ substring$ 't := }
      if$
    }
  while$
  int 
}


function{title.lowerwords}{
"a,an,and,of,the,for,in,to,over,from,on,or,so,than,that,this,as,but,with,by,at,down,up,upon,al,ale,aus,aux,d'Analyse,d'Analystes,d'Architecture,d'Etudes,d'Histoire,da,dans,de,degli,dei,del,"
"dell',dell'Accademia,dell'Istituto,dell'Universita,della,delle,dem,der,des,detta,di,die,din,dlia,do,du,e,eXpress,ed,ego,el,em,en,et,fur,i,iz,l'Academie,l'Age,l'Antiquite," *
"l'Approximation,l'Ecole,l'Histoire,l'I.S.U.P.,l'INSA,l'IREM,l'Indirizzo,l'Institut,l'Institute,l'UFR,l'Union,l'Universite,la,las,les,na,nella,per,po,si,sue,sur,ta,tes,und,van,voor,zu,zum,zur" *
}

FUNCTION {upercase.first.letters}{
	't :=
	"" 's :=
  #1 'int :=
  #1 'count :=
  list.string  'v :=
  "" 'b :=
  title.lowerwords 'list.string :=	
 %  		"title =" t * top$

  t text.length$ 'slen :=
  
    {count slen = not }
    {t int #1 substring$ " " =
      	{
	        int #1 - 'int :=
      	  t #1 int substring$ 'b :=
          
          %jei zodis ne sarase, jo pirmaja raide padarom didziaja
      	  b is.in.list not
      	  	{
      	  		b "u" change.case$ "t" change.case$ 'b :=
      	  	}
      	  	'skip$
      	  if$
      	  
	        int #1 + 'int :=

      	  s b " " *  * 's :=
	        int #1 + 'int :=
   		    t int global.max$ substring$ 't :=
				  #0 'int :=
      	}
      	'skip$
      if$	
      int #1 + 'int :=
			count #1 + 'count :=
%			"count=" count int.to.str$ * " slen=" * slen int.to.str$ * top$
    }
  while$
  v 'list.string :=	

  s t "u" change.case$ "t" change.case$  * %top$
		
}


FUNCTION {format.title}
{ title empty$
    { "" }
    { title 
      "misc" type$ =
    	 'skip$
    	 {"t" change.case$}
      if$

%      "article" type$ =
%      "book" type$ =
%      or
%    		 {"t" change.case$}
%    		 {upercase.first.letters}
%    	if$
    }
  if$
}

FUNCTION {note.presented}
 {note #1 #9 substring$ "presented" = 
 	note #1 #9 substring$ "Presented" = 
 or}
 
FUNCTION {n.filter}
{ 't :=
  ""
    { t empty$ not }
    { t #1 #1 substring$ "," =
      t #1 #1 substring$ "\" =
      t #1 #1 substring$ "~" =
      or or
            {  "" *
                  t #2 global.max$ substring$ 't :=
            }
        { t #1 #1 substring$ *
          t #2 global.max$ substring$ 't :=
        }
      if$
    }
  while$
}


FUNCTION {format.month}
{ month empty$
'skip$
{month sort.format.month}
if$
}
FUNCTION {formatpatent.date}
{ year empty$
    'skip$
    { month empty$
       { year }
        {format.month " " * year *}
      if$
    }
  if$
}

FUNCTION {bcomment}
{ duplicate$ empty$
    { pop$ "" }
    { #0 bother =
    	 		'skip$
			    { "\bcomment{" swap$ * "}" * }
	    if$
    }
  if$
}


FUNCTION {tie.or.space.connect}
{ duplicate$ text.length$ #3 <
    { "~" }
    { " " }
  if$
  swap$ * *
}

FUNCTION {format.volume}
{ volume empty$
    { "book" type$ =
    		{number empty$
    			{""}
    			{"Vol. " number bseriesno *}
    			if$
    		}
    		{""} 
      if$
    }
    {"Vol. " volume bseriesno *}
  if$
}



FUNCTION {format.series}
{ series empty$
		{""} 
    { #0 bother =
			{"\textit{"}
		    {"\bsertitle{"}
    	if$
    	series  "t" change.case$ * "}" *
    }
  if$
}
FUNCTION {format.ser.vol}
{   volume empty$
    	'skip$
    	{
			series empty$
				'insert.comma
				'skip$ 
    		if$
    		format.volume output
    	}
    if$	

	series empty$
		'skip$ 
    	{ 
		    volume empty$
		    	{""}
    			{"of "}
    		if$	
		  #0 bother =
			{"\textit{" }
			{"\bsertitle{" }
    	  if$
    	 *  series "t" change.case$ * "}" * output
    	}
  	if$
}

FUNCTION {format.edition}
{ edition empty$
    { "" }
    { "" 'v :=
			"" 'l :=    
			"" 'f :=    
    	edition "l" change.case$ 's :=
 				"1" s =
 				"first" s =  			
   			or
   				{
   					"1" 'v :=
						"st" 'l :=  
   				}
   				{
 						"2" s =
 						"second" s =  			
   					or
   						{
   							"2" 'v :=
								"nd" 'l :=  
   						}
   						{
 								"3" s =
 								"third" s =  			
   							or
   								{
   									"3" 'v :=
										"rd" 'l :=  
   								}
   								{
 										"4" s =
 										"fourth" s =  			
   									or
   										{
   											"4" 'v :=
												"th" 'l :=  
   										}
   										{
 												"5" s =
 												"fifth" s =  			
   											or
   												{
   													"5" 'v :=
														"th" 'l :=  
   												}
   												{
 														"6" s =
 														"sixth" s =  			
										   			or
   														{
   															"6" 'v :=
																"th" 'l :=  
										   				}
										   				{
												 				"7" s =
												 				"seventh" s =  			
												   			or
												   				{
												   					"7" 'v :=
																		"th" 'l :=  
												   				}
												   				{
														 				"8" s =
														 				"eighth" s =  			
														   			or
														   				{
														   					"8" 'v :=
																				"th" 'l :=  
														   				}
														   				{
																 				"9" s =
																 				"nineth" s =  			
																   			or
																   				{
																   					"9" 'v :=
																						"th" 'l :=  
																   				}
																   				{
   																						edition "t" change.case$ 'f :=
  																 				}
																   			if$	 
														   				}
														   			if$	 
												   				}
												   			if$	 
										   				}
   													if$	 
								   				}
								   			if$	 
						   				}
						   			if$	 
				   				}
				   			if$	 
   						}
   					if$	 
   				}
   			if$	 
   		 #0 bother =		
   				{	f "" =
   						{ v l *	'f :=}
   						'skip$
   					if$
   				}
   				{	f "" =
   						{ "\bedition{" v * "}" * l *	'f :=}
   						{ "\bedition{" f * "}" *	'f :=}
   					if$
   				}
   		if$
   		f " edn." *
    }
  if$
}
FUNCTION {format.isbn}
{ isbn empty$
    { "" }
    { 	#0 bother =
		    		{isbn}
		    		{"\bisbn{"  isbn * "}" *}
		    if$
		}	
  if$
}


FUNCTION {multi.page.check}
{ 't :=
  #0 'multiresult :=
	"" 'l :=

    {t empty$ not}
    { t #1 #1 substring$  's :=
    	
      s is.num not
        { "" l = not
        		{t find.integer 
								{#1 'multiresult := }
								{#0 'multiresult := }
       		 		if$
       		 		"" 't :=
       			}
       			{
       			t #2 global.max$ substring$ 't :=
       			}
       		if$	
        }
        { l  s * 'l :=
        	t #2 global.max$ substring$ 't := 
        }
      if$
    }
  while$
  multiresult 
}
FUNCTION {clearpage}
{ 't :=
	"" 's :=
	"" 'l :=
	
    { t empty$ not }
    {
    	t #1 #1 substring$ 's :=
      s is.num not
				'skip$
        {	l  s * 'l := 	}
      if$
      t #2 global.max$ substring$ 't :=
		}
  while$
  l
       
}
FUNCTION {do.pages}
{'t :=
	"" 'j :=
	"" 'v :=
    {t empty$ not}
    { t #1 #1 substring$  's :=
      s is.num not
      s "," = not
      and
        { "" j = 
       			{
       				t #2 global.max$ substring$ 't :=
       			}
        		{t find.integer 
								{ t clearpage  'v := }
								'skip$
       		 		if$
       		 		"" 't := 
       			}
       		if$	
        }
        {	j  s * 'j :=
          	t #2 global.max$ substring$ 't := 
        }
      if$
    }
  while$
  j clearpage  'j :=
  j  bfpage "--"  * v blpage *
}


FUNCTION {format.pages}
{ pages empty$
    { "" }
    { pages multi.page.check
        {type$ "article" =
        	{""}
        	{""} 
         if$	
        	pages do.pages *
        }
        {type$ "article" =
        	{""}
        	{""} 
         if$	
        	pages clearpage bfpage *
        }

      if$
    }
  if$
}

FUNCTION {format.art.vol}
{ volume empty$
	{number empty$
		{""}
		{number bvolume}
	  if$
	}
	{volume n.filter bvolume 
		number empty$
    		{""}
     		{" (" number bissue * ")" * }
     	if$
     	*
	}
  if$

	volume empty$ number empty$ and
		{""}
		{pages empty$
			{""}
			{": "}
		 if$
		}
	if$
	*
	format.pages
  	*
}

FUNCTION {replace.tilde}
{ 't :=
  ""
    { t empty$ not }
    { t #1 #1 substring$ "~" =
            {   { t #1 #1 substring$ "~" = }
                { "\texttildelow " *
                  t #2 global.max$ substring$ 't :=
                }
              while$
            }
        { t #1 #1 substring$ *
          t #2 global.max$ substring$ 't :=
        }
      if$
    }
  while$
}

FUNCTION {format.url}
{ url empty$
    { "" }
    { 	#0 bother =
				    {"\url{" url replace.tilde * "}" * }
				    {"\burl{" url replace.tilde * "}" * }
		    if$
		}	
  if$
}



FUNCTION {format.doi}
{ doi empty$
	{""}
	{
	 "nodoi" is.in.list
    	{""}
  	   	{"doi:\doiurl{" doi * "}" *}
     if$
	}
  if$
}

FUNCTION {format.in.ed.booktitle}
{ 
	booktitle empty$
		'skip$
		{"In " booktitle "t" change.case$ bbtitle * output}
	if$

   	editor empty$
   		'new.sentence
   		'insert.comma
   	if$
	format.middle.editors
   	new.sentence
}


FUNCTION {format.tr.number}
{ type empty$
    { "Technical Report" }
    'type
  if$
  number empty$
    { "t" change.case$ }
    { number tie.or.space.connect }
  if$
}

FUNCTION {patent.number}
{    number empty$
		 'skip$
    { number }
  if$
}
INTEGERS { len }

FUNCTION {chop.word}
{ 's :=
  'len :=
  s #1 len substring$ =
    { s len #1 + global.max$ substring$ }
    's
  if$
}   
 
FUNCTION {format.inpres}
{ "l" change.case$ 't :=
      "in press: " #10
       "in press. " #10
        "in press " #9 t chop.word
      chop.word
     chop.word
  #1 global.max$ substring$
}

FUNCTION {bcomment.note}
{note empty$
'skip$
 {note format.inpres bcomment output}
 if$
}

FUNCTION {empty.misc.check}
{ author empty$ title empty$ howpublished empty$
  month empty$ year empty$ note empty$
  and and and and and
    { "all relevant fields are empty in " cite$ * warning$ }
    'skip$
  if$
}

FUNCTION {format.thesis.type}
{ type empty$
    'skip$
    { pop$
      type "t" change.case$
    }
  if$
}

FUNCTION {format.chapter.and.note}
{		note empty$ chapter empty$ organization empty$ and and
		'skip$
	{	chapter empty$
		"nenumeris" last.label =
		or
			{organization empty$
			 type$ "manual" =
			 or
					{note bcomment output}
					{note empty$
							{organization bcomment output}
							{organization ". " * note * bcomment output}
					 if$
					}
			 if$
			}
			{note empty$
				{"Chap. "  chapter * bcomment output}
						{		type empty$
									{ "Chap. " }
									{ type "t" change.case$ "Section" = 
									 		{	"Sect. " }
											{ "Chap. " }
										if$	
									}
								if$
										chapter * ". " * note * bcomment  output
						}
					if$
				}
			if$
	}
	if$
		
}

FUNCTION {item.pabaiga}
{
  new.sentence
  format.doi  output
  new.sentence
  type$ "unpublished" =
  		{	note empty$
  				'skip$
  				{note.presented
  						'skip$
  						{note output}
  				 if$		
  				}
  			if$	
  		}
		{
		  type$ "proceedings" =
				{author empty$ editor empty$ and
					'bcomment.note
		 			'format.chapter.and.note 
				 if$	
				}
	 			'format.chapter.and.note 
		 	if$		
 		}
	if$
	new.sentence 
  	type$ "book" =
  		'skip$
  		{format.isbn output}
  	if$	
  	new.sentence
  	format.url output
  	"." * write$ newline$
}

FUNCTION {insert.element}
{	element
	#0 bother =
  		{"{botherref}"}
  		{
	   	 type$ "article" =
			{"{barticle}"}
			'skip$
		 if$
		 type$ "book" =
		 type$ "proceedings" =
         type$ "manual" =
         type$ "booklet" =
         or or or 
			{"{bbook}"}
			'skip$
		 if$
		   
		 type$ "inbook" =
				{	"nenumeris" last.label =
					{
						author empty$
						  	{"{bbook}"}
							{"{bchapter}"}
						if$	
					}
					{ 	author empty$ editor empty$ or
					  		{"{bbook}"}
							{"{bchapter}"}
						if$	
				  	}
				    if$	
			    }
				'skip$
		 if$
		
		 type$ "incollection" =
		 type$ "inproceedings" =
		 type$ "conference" =
		 or or
		    {"{bchapter}"}
			'skip$
		 if$

   		}
  if$
   * write$ newline$
}


FUNCTION {end.element}
{ 	"\end" 'element :=
	item.pabaiga
  	insert.element
  	"\endbibitem" write$ newline$
}
FUNCTION {begin.element}
{ "\begin" 'element :=
  insert.element
}
FUNCTION {assign.global.values}{

	%%%%%%%%%% pradiniai nustatytmai: #1->ijungta, #0->isjungta  
  info empty$
    'skip$
    { info "1" =
      	{#1 'default.info :=} 
      	{#0 'default.info :=}
      if$
		}
	if$
}
FUNCTION {prin.info}{
	default.info
		{
%		"%" month=" * article.month int.to.str$ * ")" * write$ newline$
			"%style="
			"alpha" is.in.list
				{"alpha"}
				{
					"nameyear" is.in.list
						{"nameyear"}
						{"number"}
					if$
				}
			if$
			*
			", sorted="
			*	
			"unsort" is.in.list
				{"no"}
				{"yes"}
			if$
			*

			"nodoi" is.in.list
				{", other options=nodoi" *}
				'skip$
			if$
			write$ newline$
		}
		'skip$
	if$	
}

FUNCTION {settings}
{
  	set.settings not
		{ 
		  assign.global.values
		  #1 'set.settings :=
		  prin.info
		}
		'skip$
	if$
}

function{after.names}{ 	
	write$ add.period$ 
	after.block  'output.state :=
}

FUNCTION {article}
{ output.bibitem
	author empty$
	institution empty$ 
	editor empty$
	and and
	journal empty$ 
  	year empty$ 
 	or or 
		{#0 'bother :=} 
		{ 
		  volume empty$ pages  empty$ %doi empty$ not
          or %and
			  {
  			  volume empty$ pages  empty$ doi empty$ not
  			  and and   
    			  {#1 'bother :=}
		   	    {#0 'bother :=}
			    if$ 
			  } 
			  {#1 'bother :=}
        if$ 			
			} 
	if$		
	begin.element
	author empty$
    	{ editor empty$
    		'skip$
     		{format.editors output.nonnull stupid.colon}
    	  if$
    	}
    	{ format.authors after.names}
  	if$

	format.date output
  	year empty$
		'skip$
		'new.sentence
	if$
	format.title batitle "title" output.check
	new.sentence
	journal empty$
		{fjournal empty$
			'skip$
			{fjournal bjtitle  output}
		 if$	
		}
    	{journal bjtitle  output}
	if$
    volume empty$
    	'skip$
		{format.art.vol output }
		if$
	end.element
}

FUNCTION {patent}
{ output.bibitem
	#0 'bother :=
	begin.element
 	format.authors after.names
  	formatpatent.date output
	new.sentence
    format.title "title" output.check
	new.sentence
	patent.number output
	end.element
}

FUNCTION { other } { patent }

FUNCTION {book}
{ output.bibitem
	author empty$
	institution empty$ 
	organization empty$ 
	editor empty$
	and and and
	title empty$ 
    year empty$ 
 	or or 
		{#0 'bother :=} 
		{
			publisher empty$ address empty$ not and
				{#0 'bother :=} 
				{#1 'bother :=}
			if$
		} 
	if$	
	begin.element
	author empty$
    	{ editor empty$
    		'skip$
     		{format.editors output.nonnull stupid.colon}
    	  if$
    	}
    	{ format.authors after.names}
  	if$
	format.date output
	new.sentence
  
  	format.title bbtitle "title" output.check
	edition empty$
		'skip$
    	{insert.comma format.edition output}
  	if$
	new.sentence
  	format.ser.vol 
	new.sentence
    format.pub.address
	end.element      
}

FUNCTION {booklet}
{output.bibitem
	author empty$
	title empty$ 
  	year empty$ 
 	howpublished empty$  
   	or or or
		{#0 'bother :=} 
		{#1 'bother :=} 
	if$	

	begin.element
  	author empty$
 		 'skip$
  		{format.authors after.names}
  	if$
	format.date output
	new.sentence
  	format.title bbtitle "title" output.check
  	publisher empty$
  		'insert.comma
  		'skip$
  	if$	
  	format.pub.address
	end.element
}
FUNCTION {misc}
{output.bibitem
 	#0 'bother :=
	begin.element
  	author empty$
 		 'skip$
  		{format.authors after.names}
  	if$
	format.date output
	new.sentence
  	format.title "title" output.check
  	publisher empty$
  		'insert.comma
		'skip$
	if$	  
  	format.pub.address
	new.sentence
	end.element
}

FUNCTION {inbook}
{ output.bibitem

  	author empty$
	institution empty$ 
	organization empty$ 
	editor empty$
	and and and
	series empty$
	chapter empty$
	and
  	year empty$ 
 	or or
		{#0 'bother :=} 
		{
			publisher empty$ address empty$ not and
				{#0 'bother :=} 
				{#1 'bother :=}
			if$
		} 
	if$	

	chapter empty$
		{	"" 'last.label :=}
  		{ 	chapter text.length$ #10 <
  			%check.chapter 
				{	"" 'last.label :=}
  				{	"nenumeris" 'last.label :=}
			if$
  		}
  	if$
	begin.element
	author empty$
    	{ editor empty$
    		'skip$
     		{format.editors output.nonnull stupid.colon}
    	  if$
    	}
    	{ format.authors after.names}
  	if$
	format.date output
	new.sentence
    
    title empty$
  		{
  		 chapter empty$
  		 	'skip$
   		 	{"nenumeris" last.label =
				{"In " chapter bbtitle * output}
				'skip$
		 	 if$
		 	}
		 if$  		
  		}
  		{format.title bctitle output}
   	if$
	new.sentence

    insert.comma
    format.edition output
	insert.comma
	
	author empty$ 
		'skip$
   		'format.middle.editors 
    if$	
	insert.comma
  	format.ser.vol 
	insert.comma
    format.pages output
	new.sentence
    format.pub.address
  	end.element
}

FUNCTION {incollection}
{ output.bibitem
  author empty$
	institution empty$ 
	and
	booktitle empty$ 
	title empty$
  	year empty$ 
 	or or or
		{#0 'bother :=} 
		{
			publisher empty$ address empty$ not and
				{#0 'bother :=} 
				{#1 'bother :=}
			if$
		} 
	if$	
	begin.element
	author empty$
		'skip$	
		{format.authors after.names}
	if$		 
	format.date output
	new.sentence
  	format.title bctitle "title" output.check
	insert.comma
	format.edition output
	new.sentence
	format.in.ed.booktitle 
	new.sentence
  	format.ser.vol 
  	pages empty$
    	'new.sentence
  		'insert.comma
    if$
    format.pages output
    new.sentence
    format.pub.address
	end.element
}

FUNCTION {inproceedings}
{ output.bibitem
	author empty$
	institution empty$ 
	and
	booktitle empty$ 
	series empty$
	and
	year empty$ 
 	or or
		{#0 'bother :=} 
		{#1 'bother :=} 
	if$	
	begin.element
  	format.authors after.names
	format.date output
	new.sentence
  	format.title bctitle  "title" output.check
    new.sentence
	format.in.ed.booktitle 
	new.sentence
  	format.ser.vol 
	insert.comma
    format.pages output
    new.sentence
    format.pub.address
	end.element
}

FUNCTION {conference}{inproceedings}

FUNCTION {manual}
{ output.bibitem

	author empty$
	organization empty$ 
	title empty$ 
  	year empty$ 
 	address  empty$ 
  
   	or or or or
		{#0 'bother :=} 
		{#1 'bother :=} 
	if$	
	begin.element

  	author empty$
    	{ organization empty$
        	'skip$
        	{ organization binstitute output.nonnull stupid.colon}
      	  if$
    	}
    	{ format.authors after.names}
	if$
	format.date output
	new.sentence
  		
	title empty$
  		'skip$
  		{format.title bbtitle output
 			}
   	if$
  	edition empty$
    	{new.sentence}
 		{insert.comma}
	if$
  	format.edition output
    new.sentence
    format.pages output
    new.sentence
    format.pub.address
	end.element
}


FUNCTION {phdthesis}
{output.bibitem
	#0 'bother :=

	begin.element
  	author empty$
 		 'skip$
  		{format.authors after.names}
  	if$
	format.date output
	new.sentence
  
  	format.title "title" output.check
	new.sentence
  	type$ "mastersthesis"  =
  		{"Master's thesis" format.thesis.type output.nonnull}
  		{"PhD diss" format.thesis.type output.nonnull}
  	if$		
  	school empty$
    	'skip$
     	{ insert.comma }
  	if$
  	school "school" output.check
  	address empty$
     	'skip$
     	{ insert.comma address output}
  	if$
	end.element
}
FUNCTION {mastersthesis}{phdthesis}


FUNCTION {proceedings}
{ output.bibitem
	author empty$
	institution empty$ 
	organization empty$ 
	editor empty$
	and and and
	booktitle empty$ 
	series empty$
	and 
  	year empty$ 
 	or or 
		{#0 'bother :=} 
		{
			publisher empty$ address empty$ not and
				{#0 'bother :=} 
				{#1 'bother :=}
			if$
		} 
	if$	
	begin.element
  	author empty$
   		{ 	editor empty$
   			 	{organization binstitute "organization" output.check stupid.colon}
				{ format.editors output.nonnull stupid.colon}
  			if$ 
  		}
    	{ format.authors after.names}
  	if$
    
	format.date output
	new.sentence
  	format.title bctitle "title" output.check
 	title empty$ 
   	  	'skip$
    	{insert.comma}
	if$
    
  	booktitle empty$
  		'skip$
  		{"In " booktitle bbtitle * output}
  	if$    
	new.sentence
    format.ser.vol 
	insert.comma
    format.pages output
    new.sentence
    format.pub.address
	end.element
}	

FUNCTION {techreport}
{output.bibitem
	#0 'bother :=

	begin.element
  	author empty$
 		'skip$
  		{format.authors after.names}
  	if$
	format.date output
	new.sentence
  
  	format.title "title" output.check
	insert.comma
  	format.tr.number output.nonnull
  	institution empty$
    	'skip$
     	{ insert.comma }
  	if$
  	institution "institution" output.check
  	address empty$
    	'skip$
     	{ insert.comma }
  	if$
  	address output
	end.element
}

FUNCTION {unpublished}
{output.bibitem
	#0 'bother :=

	begin.element
  	author empty$
 		'skip$
  		{format.authors after.names}
  	if$
  	format.date output
	new.sentence
  	format.title "title" output.check
  	title empty$
  		'skip$
  		{new.sentence}
  	if$
  	note empty$
    	'skip$
  		{note.presented 
  			{note output}
    		'skip$
  		 if$
  		}
  	if$
	end.element
}

FUNCTION {default.type} { unpublished }

MACRO {jan} {"January"}

MACRO {feb} {"February"}

MACRO {mar} {"March"}

MACRO {apr} {"April"}

MACRO {may} {"May"}

MACRO {jun} {"June"}

MACRO {jul} {"July"}

MACRO {aug} {"August"}

MACRO {sep} {"September"}

MACRO {oct} {"October"}

MACRO {nov} {"November"}

MACRO {dec} {"December"}

READ

FUNCTION {sortify}
{ purify$
  "l" change.case$
}

INTEGERS { et.al.char.used }

FUNCTION {initialize.et.al.char.used}
{ #0 'et.al.char.used :=
}

FUNCTION {assign.opt}{
  % priskiriu options lauka, kad galeciau i(is)jungti "unsort"

  "settings" type$ =
  	{options empty$
		'skip$
  		{options 'list.string :=}
  	 if$
  	}
  	'skip$
  if$
}

FUNCTION {set.default.opt}
{	"nameyear" 'list.string :=}

EXECUTE {set.default.opt}

ITERATE {assign.opt}
EXECUTE {initialize.et.al.char.used}

FUNCTION {alpha.format.lab.names}
{ 's :=
  s num.names$ 'numnames :=
  numnames #1 >
    { numnames #4 >
	{ #3 'namesleft := }
	{ numnames 'namesleft := }
      if$
      #1 'nameptr :=
      ""
	{ namesleft #0 > }
	{ nameptr numnames =
	    { s nameptr "{ff }{vv }{ll}{ jj}" format.name$ "others" =
		{ "+" *
		  #1 'et.al.char.used :=
		}
		{ s nameptr "{v{}}{l{}}" format.name$ * }
	      if$
	    }
	    { s nameptr "{v{}}{l{}}" format.name$ * }
	  if$
	  nameptr #1 + 'nameptr :=
	  namesleft #1 - 'namesleft :=
	}
      while$
      numnames #4 >
	{ "+" *
	  #1 'et.al.char.used :=
	}
	'skip$
      if$
    }
    { s #1 "{v{}}{l{}}" format.name$
      duplicate$ text.length$ #2 <
	{ pop$ s #1 "{ll}" format.name$ #3 text.prefix$ }
	'skip$
      if$
    }
  if$
}

FUNCTION {standart.format.lab.names}
{ 's :=
  s #1 "{vv~}{ll}" format.name$
  s num.names$ duplicate$
  #2 >
    { pop$ " et~al." * }
    { #2 <
        'skip$
        { s #2 "{ff }{vv }{ll}{ jj}" format.name$ "others" =
            { " et~al." * }
            { " and " * s #2 "{vv~}{ll}" format.name$ * }
          if$
        }
      if$
    }
  if$
}
FUNCTION {format.lab.names}{
	"alpha" is.in.list
		'alpha.format.lab.names
	  'standart.format.lab.names
	if$
}

FUNCTION {author.key.label}
{ author empty$
    { key empty$
	{ cite$ #1 #3 substring$ }
	{ key #3 text.prefix$ }
      if$
    }
    { author format.lab.names }
  if$
}

FUNCTION {author.editor.key.label}
{ author empty$
    { editor empty$
	{ key empty$
%	    { cite$ #1 #3 substring$ }
	    { "zzz" }
	    { key #3 text.prefix$ }
	  if$
	}
	{ editor format.lab.names }
      if$
    }
    { author format.lab.names }
  if$
}

FUNCTION {author.key.organization.label}
{ author empty$
    { key empty$
	{ organization empty$
%	    { cite$ #1 #3 substring$ }
	    { "zzz" }
	    { "The " #4 organization chop.word #3 text.prefix$ }
	  if$
	}
	{ key #3 text.prefix$ }
      if$
    }
    { author format.lab.names }
  if$
}

FUNCTION {editor.key.organization.label}
{ editor empty$
    { key empty$
	{ organization empty$
%	    { cite$ #1 #3 substring$ }
	    { "zzz" }
	    { "The " #4 organization chop.word #3 text.prefix$ }
	  if$
	}
	{ key #3 text.prefix$ }
      if$
    }
    { editor format.lab.names }
  if$
}

FUNCTION {calc.short.authors}
{ type$ "book" =
  type$ "inbook" =
  or
    'author.editor.key.label
    { type$ "proceedings" =
        'editor.key.organization.label
        { type$ "manual" =
            'author.key.organization.label
            'author.key.label
          if$
        }
      if$
    }
  if$
  'short.list :=
}

FUNCTION {calc.label}
{ calc.short.authors
  short.list

  "alpha" is.in.list
  {
    duplicate$
    year field.or.null purify$ #-1 #2 substring$
    *
    'label :=
    year field.or.null purify$ #-1 #4 substring$
    *
    sortify 'sort.label :=
  }
  {
    "("
    *
    year duplicate$ empty$
    short.list key field.or.null = or
      { pop$ "" }
      'skip$
    if$
    *
    'label :=
    label 'sort.label :=
  } 
  if$
}

FUNCTION {sort.format.names}
{ 's :=
  #1 'nameptr :=
  ""
  s num.names$ 'numnames :=
  numnames 'namesleft :=
    { namesleft #0 > }
    { nameptr #1 >
        { "   " * 
          "alpha" is.in.list
            'skip$
            {numnames int.to.str$ * "   " *}
          if$
        }
        'skip$
      if$
      s nameptr "{vv{ } }{ll{ }}{  ff{ }}{  jj{ }}" format.name$ 't :=
      nameptr numnames = 
      t "others" = 
      and
        { "et al" * }
        { t sortify * }
      if$
		#3 numnames  <
		"alpha" is.in.list not
		and
  			{#0 'namesleft :=
  				 	" zzz   " *
  			}    
	      {
	     	  nameptr #1 + 'nameptr :=
  	    	namesleft #1 - 'namesleft :=
  	    }
  	  if$  	
    }
  while$
}

FUNCTION {sort.format.title}
{ 't :=
  "A " #2
    "An " #3
      "The " #4 t chop.word
    chop.word
  chop.word
  sortify
  #1 global.max$ substring$
}

FUNCTION {author.sort}
{ author empty$
    { key empty$
        { "to sort, need author or key in " cite$ * warning$
          "zzz"
        }
        { key sortify }
      if$
    }
    { author sort.format.names }
  if$
}

FUNCTION {author.editor.sort}
{ author empty$
    { editor empty$
        { key empty$
            { "to sort, need author, editor, or key in " cite$ * warning$
              "z"
            }
            { key sortify }
          if$
        }
        { editor sort.format.names }
      if$
    }
    { author sort.format.names }
  if$
}

FUNCTION {author.organization.sort}
{ author empty$
    { organization empty$
        { key empty$
            { "to sort, need author, organization, or key in " cite$ * warning$
              "z"
            }
            { key sortify }
          if$
        }
        { "The " #4 organization chop.word sortify }
      if$
    }
    { author sort.format.names }
  if$
}

FUNCTION {editor.organization.sort}
{ editor empty$
    { organization empty$
        { key empty$
            { "to sort, need editor, organization, or key in " cite$ * warning$
              "z"
            }
            { key sortify }
          if$
        }
        { "The " #4 organization chop.word sortify }
      if$
    }
    { editor sort.format.names }
  if$
}

FUNCTION {presort}
{ calc.label
  sort.label sortify
  "    "
  *
  type$ "book" =
  type$ "inbook" =
  or
 		{author empty$
   		'editor.organization.sort
      'author.organization.sort
     if$
    }
    { type$ "proceedings" =
      type$ "incollection" =
       or
    		{author empty$
        		'editor.organization.sort
            'author.organization.sort
        if$
        }
        { type$ "manual" =
            'author.organization.sort
            'author.sort
          if$
        }
      if$
    }
  if$
  "    "
  *
  year field.or.null sortify
  *
  "    "
  *
  title field.or.null
  sort.format.title
  *
  #1 entry.max$ substring$ 'sort.label :=
  sort.label *
  #1 entry.max$ substring$ 'sort.key$ :=
  
  "settings" type$ =
  	{"aaa"}
  	{"unsort" is.in.list
    	{"bb"}
    	{"alpha" is.in.list
    		{sort.key$}
    		{sort.label}
      	if$  
   		}
  	 if$
  	}
  	if$
  'sort.key$ :=
}


ITERATE {presort}

SORT

INTEGERS { longest.label.width last.extra.num number.label }

FUNCTION {initialize.longest.label}
{ "" 'longest.label :=
  #0 int.to.chr$ 'last.label :=
  "" 'j :=
  #0 'longest.label.width :=
  #0 'last.extra.num :=
  #0 'number.label :=
}

FUNCTION {forward.pass}
{ last.label label =
    { last.extra.num #1 + 'last.extra.num :=
      last.extra.num int.to.chr$ 'extra.label :=
    }
    { "a" chr.to.int$ 'last.extra.num :=
      "" 'extra.label :=
      label 'last.label :=
    }
  if$
  number.label #1 + 'number.label :=
%  cite$ "  " * extra.label * " label=" * label * top$
}

FUNCTION {reverse.pass}
{ j "b" =
    { "a" 'extra.label := }
    'skip$
  if$
  extra.label 'j :=
  label extra.label * 'label :=
}

EXECUTE {initialize.longest.label}

ITERATE {forward.pass}

REVERSE {reverse.pass}

FUNCTION {write.preamble}
{ "\begin{thebibliography}{" number.label int.to.str$ * "}" * write$ newline$
	"% BibTex style file: spr-chicago.bst, 2011-02-21" write$ newline$
	"\ifx \bisbn   \undefined \def \bisbn  #1{ISBN #1}\fi" write$ newline$
	"\ifx \binits  \undefined \def \binits#1{#1} \fi" write$ newline$
	"\ifx \bauthor  \undefined \def \bauthor#1{#1} \fi" write$ newline$
	"\ifx \bjtitle  \undefined \def \bjtitle#1{\textit{#1}}\fi" write$ newline$
	"\ifx \batitle  \undefined \def \batitle#1{#1} \fi" write$ newline$
	"\ifx \bctitle  \undefined \def \bctitle#1{#1} \fi" write$ newline$
	"\ifx \bvolume  \undefined \def \bvolume#1{#1}\fi" write$ newline$
	"\ifx \byear  \undefined \def \byear#1{#1} \fi" write$ newline$
	"\ifx \bissue  \undefined \def \bissue#1{#1} \fi" write$ newline$
	"\ifx \bfpage  \undefined \def \bfpage#1{#1} \fi" write$ newline$
	"\ifx \blpage  \undefined \def \blpage #1{#1} \fi" write$ newline$
	"\ifx \burl  \undefined \def \burl#1{#1} \fi" write$ newline$
	"\ifx \doiurl  \undefined \def \doiurl#1{#1} \fi" write$ newline$
	"\ifx \betal  \undefined \def \betal{et al.} \fi" write$ newline$
	"\ifx \binstitute  \undefined \def \binstitute#1{#1} \fi" write$ newline$
	"\ifx \beditor  \undefined \def \beditor#1{#1} \fi" write$ newline$
	"\ifx \bpublisher  \undefined \def \bpublisher#1{#1} \fi" write$ newline$
	"\ifx \bbtitle  \undefined \def \bbtitle#1{\textit{#1}} \fi" write$ newline$
	"\ifx \bedition  \undefined \def \bedition#1{#1} \fi" write$ newline$
	"\ifx \bseriesno  \undefined \def \bseriesno#1{#1} \fi" write$ newline$
	"\ifx \blocation  \undefined \def \blocation#1{#1} \fi" write$ newline$
	"\ifx \bsertitle  \undefined \def \bsertitle#1{\textit{#1}} \fi" write$ newline$
	"\ifx \bsnm \undefined \def \bsnm#1{#1} \fi" write$ newline$
	"\ifx \bsuffix \undefined \def \bsuffix#1{#1} \fi" write$ newline$
	"\ifx \bparticle \undefined \def \bparticle#1{#1} \fi" write$ newline$
	"\ifx \barticle \undefined \def \barticle#1{#1} \fi" write$ newline$
	
}


FUNCTION {begin.bib}
{ preamble$ empty$
    'skip$
    { 
    	preamble$ write$ newline$ 
    }
  if$
  
  write.preamble
  "\ifx \botherref \undefined \def \botherref #1{#1} \fi" write$ newline$
  "\ifx \url \undefined \def \url#1{#1} \fi" write$ newline$
	"\ifx \bchapter \undefined \def \bchapter#1{#1} \fi" write$ newline$
	"\ifx \bbook \undefined \def \bbook#1{#1} \fi" write$ newline$
	"\ifx \bcomment \undefined \def \bcomment#1{#1} \fi" write$ newline$
	"\ifx \oauthor \undefined \def \oauthor#1{#1} \fi" write$ newline$
	"\ifx \citeauthoryear \undefined \def \citeauthoryear#1{#1} \fi" write$ newline$
	"\ifx \texttildelow  \undefined \def \texttildelow{\symbol{126}} \fi" write$ newline$
	"\def \endbibitem {}" write$ newline$
	"\ifx \bconflocation  \undefined \def \bconflocation#1{#1} \fi" write$ newline$
}
EXECUTE {begin.bib}

EXECUTE {init.state.consts}

ITERATE {call.type$}

FUNCTION {end.bib}
{ newline$
 "\end{thebibliography}" write$ newline$
}

EXECUTE {end.bib}




