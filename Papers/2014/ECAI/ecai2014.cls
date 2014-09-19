% documentclass ecai2014
%
% This is file `ecai2014.cls', the recommended style file for ECAI-2014
% submission and camera-ready copy, for use with latex2e 
% in native mode. It is the same as `ecai2004.cls' used for ECAI-2004.

% This file is an adaption of ecai98.cls. It provides the same style 
% as ecai98.cls but removes any footer.
% ecai98.cls was created by merging the ECAI-96 document style with the 
% latex2e article class. It has inherited most of the features (and bugs) 
% of the ECAI-96 document style, but only promises to approximate that style.

% For users without access to latex2e, a style file for latex209
% is also available. This works with latex209 (but not with latex2e).

% Both these style files are available via
%   http://www.ai.univie.ac.at/ecai/latex

% Authorship and copyright:
% latex2e article.cls - copyright, the LaTeX3 project
% latex2e size10.clo  - copyright, the LaTeX3 project
% ecai96.sty          - based on original 209 aritcle style by Leslie
%                       Lamport, successively modified by Oliver Ludwig,
%                       Geeti Granger and Jenny Smith.
% ecai98.cls          - copyright 1998, Roger Evans, University of
%                       Brighton
% ecai2000.cls        - copyright 2000, Werner Horn, Austrian Research
%                       Institute for Artificial Intelligence
% ecai2002.cls        - copyright 2002, Frank van Harmelen,
%                       Vrije Universiteit Amsterdam, 

% This file is distributed in the hope that it will be useful,
% but WITHOUT ANY WARRANTY; without even the implied warranty of
% MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.

% This file is NOT SUPPORTED.
% Comments or bugs may be reported to ecai2004@dsic.upv.es

% ----------------------------------------------------------------------

\ProvidesClass{ecai2014}
              [2002/03/06 v01 ECAI-2004 document class]
\newcommand\@ptsize{}
\newif\if@restonecol
\newif\if@titlepage
\@titlepagefalse
\if@compatibility\else
\DeclareOption{a4paper}
   {\setlength\paperheight {297mm}%
    \setlength\paperwidth  {210mm}}
\DeclareOption{a5paper}
   {\setlength\paperheight {210mm}%
    \setlength\paperwidth  {148mm}}
\DeclareOption{b5paper}
   {\setlength\paperheight {250mm}%
    \setlength\paperwidth  {176mm}}
\DeclareOption{letterpaper}
   {\setlength\paperheight {11in}%
    \setlength\paperwidth  {8.5in}}
\DeclareOption{legalpaper}
   {\setlength\paperheight {14in}%
    \setlength\paperwidth  {8.5in}}
\DeclareOption{executivepaper}
   {\setlength\paperheight {10.5in}%
    \setlength\paperwidth  {7.25in}}
\DeclareOption{landscape}
   {\setlength\@tempdima   {\paperheight}%
    \setlength\paperheight {\paperwidth}%
    \setlength\paperwidth  {\@tempdima}}
\fi
\if@compatibility
  \renewcommand\@ptsize{0}
\else
\DeclareOption{10pt}{\renewcommand\@ptsize{0}}
\fi
\DeclareOption{11pt}{\renewcommand\@ptsize{1}}
\DeclareOption{12pt}{\renewcommand\@ptsize{2}}
\if@compatibility\else
\DeclareOption{oneside}{\@twosidefalse \@mparswitchfalse}
\fi
\DeclareOption{twoside}{\@twosidetrue  \@mparswitchtrue}
\DeclareOption{draft}{\setlength\overfullrule{5pt}}
\if@compatibility\else
\DeclareOption{final}{\setlength\overfullrule{0pt}}
\fi
\DeclareOption{titlepage}{\@titlepagetrue}
\if@compatibility\else
\DeclareOption{notitlepage}{\@titlepagefalse}
\fi
\if@compatibility\else
\DeclareOption{onecolumn}{\@twocolumnfalse}
\fi
\DeclareOption{twocolumn}{\@twocolumntrue}
\DeclareOption{leqno}{\input{leqno.clo}}
\DeclareOption{fleqn}{\input{fleqn.clo}}
% removed because the definition upsets 1994 latex2e systems
%\DeclareOption{openbib}{%
%  \AtEndOfPackage{%
%   \renewcommand\@openbib@code{%
%      \advance\leftmargin\bibindent
%      \itemindent -\bibindent
%      \listparindent \itemindent
%      \parsep \z@
%      }%
%   \renewcommand\newblock{\par}}%
%}
\ExecuteOptions{a4paper,twoside,twocolumn,final}
\ProcessOptions

%  --  here we instert a modified version of size10.clo, reduced to 9pt
%      plus one or two other little changes

\renewcommand\normalsize{%
   \@setfontsize\normalsize\@ixpt{11}
   \abovedisplayskip 9\p@ \@plus1.8\p@ \@minus4.5\p@
   \belowdisplayskip \abovedisplayskip
   \abovedisplayshortskip  \z@ plus2.7\p@
   \belowdisplayshortskip  5.4\p@ plus2.7\p@ minus3\p@
   \let\@listi\@listI}
\normalsize
\newcommand\small{%
   \@setfontsize\small\@ixpt{9.9}%
   \abovedisplayskip 7.7\p@ \@plus2.7\p@ \@minus3.6\p@
   \abovedisplayshortskip \z@ \@plus1.8\p@
   \belowdisplayshortskip 3.6\p@ \@plus1.8\p@ \@minus1.8\p@
   \def\@listi{\leftmargin\leftmargini
               \topsep 3.6\p@ \@plus1.8\p@ \@minus1.8\p@
               \parsep 1.8\p@ \@plus\p@ \@minus\p@
               \itemsep \parsep}%
   \belowdisplayskip \abovedisplayskip
}
\newcommand\footnotesize{%
   \@setfontsize\footnotesize\@viiipt{8.6}%
   \abovedisplayskip 5.4\p@ \@plus1.8\p@ \@minus3.6\p@
   \abovedisplayshortskip \z@ \@plus\p@
   \belowdisplayshortskip 2.7\p@ \@plus\p@ \@minus1.8\p@
   \def\@listi{\leftmargin\leftmargini
               \topsep 2.7\p@ \@plus\p@ \@minus\p@
               \parsep 1.8\p@ \@plus\p@ \@minus\p@
               \itemsep \parsep}%
   \belowdisplayskip \abovedisplayskip
}
\newcommand\scriptsize{\@setfontsize\scriptsize{7.2}\@vipt}
\newcommand\tiny{\@setfontsize\tiny\@vpt\@vpt}
\newcommand\large{\@setfontsize\large\@xipt{12}}
\newcommand\Large{\@setfontsize\Large\@xiipt{14}}
\newcommand\LARGE{\@setfontsize\LARGE\@xivpt{18}}
\newcommand\huge{\@setfontsize\huge\@xviipt{22}}
\newcommand\Huge{\@setfontsize\Huge\@xxpt{25}}
\if@twocolumn
  \setlength\parindent{1em}
\else
  \setlength\parindent{15\p@}
\fi
\setlength\smallskipamount{2.7\p@ \@plus 0.9\p@ \@minus 0.9\p@}
\setlength\medskipamount{5.4\p@ \@plus 1.8\p@ \@minus 1.8\p@}
\setlength\bigskipamount{10.8\p@ \@plus 3.6\p@ \@minus 3.6\p@}
\setlength\headheight{0\p@}
\setlength\headsep   {0\p@}
\setlength\topskip   {1\p@}
\setlength\footskip{24\p@}
\if@compatibility \setlength\maxdepth{4\p@} \else
\setlength\maxdepth{.5\topskip} \fi
%\if@compatibility
  \if@twocolumn
    \setlength\textwidth{42.5pc}
  \else
    \setlength\textwidth{345\p@}
  \fi
%\else
%  \setlength\@tempdima{\paperwidth}
%  \addtolength\@tempdima{-2in}
%  \setlength\@tempdimb{345\p@}
%  \if@twocolumn
%    \ifdim\@tempdima>2\@tempdimb\relax
%      \setlength\textwidth{2\@tempdimb}
%    \else
%      \setlength\textwidth{\@tempdima}
%    \fi
%  \else
%    \ifdim\@tempdima>\@tempdimb\relax
%      \setlength\textwidth{\@tempdimb}
%    \else
%      \setlength\textwidth{\@tempdima}
%    \fi
%  \fi
%\fi
\if@compatibility\else
  \@settopoint\textwidth
\fi
%\if@compatibility
%  \setlength\textheight{43\baselineskip}
%\else
%  \setlength\@tempdima{\paperheight}
%  \addtolength\@tempdima{-2in}
%  \addtolength\@tempdima{-1.5in}
%  \divide\@tempdima\baselineskip
%  \@tempcnta=\@tempdima
%  \setlength\textheight{\@tempcnta\baselineskip}
%\fi
%\addtolength\textheight{\topskip}

\newdimen\ftextheight
\newdimen\ntextheight
\ntextheight 671\p@
\ftextheight\ntextheight
\advance\ftextheight -42\p@


\if@twocolumn
 \setlength\marginparsep {0\p@}
\else
  \setlength\marginparsep{11\p@}
\fi
\setlength\marginparpush{5\p@}
%\if@compatibility
  \if@twoside
     \setlength\oddsidemargin   {44\p@}
     \setlength\evensidemargin  {82\p@}
     \setlength\marginparwidth {107\p@}
  \else
     \setlength\oddsidemargin   {63\p@}
     \setlength\evensidemargin  {63\p@}
     \setlength\marginparwidth  {90\p@}
  \fi
  \if@twocolumn
     \setlength\oddsidemargin  {12\p@}
%     \addtolength\oddsidemargin  {-3.2mm}
     \setlength\evensidemargin {12\p@}
%     \addtolength\evensidemargin  {-3.2mm}
     \setlength\marginparwidth {0\p@}
  \fi
%\else
%  \if@twoside
%    \setlength\@tempdima        {\paperwidth}
%    \addtolength\@tempdima      {-\textwidth}
%    \setlength\oddsidemargin    {.4\@tempdima}
%    \addtolength\oddsidemargin  {-1in}
%    \setlength\marginparwidth   {.6\@tempdima}
%    \addtolength\marginparwidth {-\marginparsep}
%    \addtolength\marginparwidth {-0.4in}
%  \else
%    \setlength\@tempdima        {\paperwidth}
%    \addtolength\@tempdima      {-\textwidth}
%    \setlength\oddsidemargin    {.5\@tempdima}
%    \addtolength\oddsidemargin  {-1in}
%    \setlength\marginparwidth   {.5\@tempdima}
%    \addtolength\marginparwidth {-\marginparsep}
%    \addtolength\marginparwidth {-0.4in}
%    \addtolength\marginparwidth {-.4in}
%  \fi
%  \ifdim \marginparwidth >2in
%     \setlength\marginparwidth{2in}
%  \fi
%  \@settopoint\oddsidemargin
%  \@settopoint\marginparwidth
%  \setlength\evensidemargin  {\paperwidth}
%  \addtolength\evensidemargin{-2in}
%  \addtolength\evensidemargin{-\textwidth}
%  \addtolength\evensidemargin{-\oddsidemargin}
%  \@settopoint\evensidemargin
%\fi
%\if@compatibility
  \setlength\topmargin{27\p@}
  \addtolength\topmargin{-9.8mm}
%\else
%  \setlength\topmargin{\paperheight}
%  \addtolength\topmargin{-2in}
%  \addtolength\topmargin{-\headheight}
%  \addtolength\topmargin{-\headsep}
%  \addtolength\topmargin{-\textheight}
%  \addtolength\topmargin{-\footskip}     % this might be wrong!
%  \addtolength\topmargin{-.5\topmargin}
%  \@settopoint\topmargin
%\fi
\setlength\footnotesep{6.65\p@}
\setlength{\skip\footins}{9\p@ \@plus 4\p@ \@minus 2\p@}
\setlength\floatsep    {11\p@ \@plus 2\p@ \@minus 4\p@}
\setlength\textfloatsep{11\p@ \@plus 2\p@ \@minus 2\p@}
\setlength\intextsep   {11\p@ \@plus 2\p@ \@minus 2\p@}
\setlength\dblfloatsep    {11\p@ \@plus 2\p@ \@minus 2\p@}
\setlength\dbltextfloatsep{11\p@ \@plus 2\p@ \@minus 4\p@}
\setlength\@fptop{0\p@ \@plus 1fil}
\setlength\@fpsep{8\p@ \@plus 2fil}
\setlength\@fpbot{0\p@ \@plus 1fil}
\setlength\@dblfptop{0\p@ \@plus 1fil}
\setlength\@dblfpsep{8\p@ \@plus 2fil}
\setlength\@dblfpbot{0\p@ \@plus 1fil}
\setlength\partopsep{2\p@ \@plus 1\p@ \@minus 1\p@}
\def\@listi{\leftmargin\leftmargini
            \parsep 0\p@
            \topsep 8\p@ \@plus2\p@ \@minus4\p@
            \itemsep 0\p@}
\let\@listI\@listi
\@listi
\def\@listii {\leftmargin\leftmarginii
              \labelwidth\leftmarginii
              \advance\labelwidth-\labelsep
              \topsep    4\p@ \@plus2\p@ \@minus\p@
              \parsep    02\p@
              \itemsep   \parsep}
\def\@listiii{\leftmargin\leftmarginiii
              \labelwidth\leftmarginiii
              \advance\labelwidth-\labelsep
              \topsep    2\p@ \@plus\p@\@minus\p@
              \parsep    \z@
              \partopsep \p@ \@plus\z@ \@minus\p@
              \itemsep   \topsep}
\def\@listiv {\leftmargin\leftmarginiv
              \labelwidth\leftmarginiv
              \advance\labelwidth-\labelsep
              \parsep \z@ \itemsep \parsep}
\def\@listv  {\leftmargin\leftmarginv
              \labelwidth\leftmarginv
              \advance\labelwidth-\labelsep
              \parsep \z@ \itemsep \parsep}
\def\@listvi {\leftmargin\leftmarginvi
              \labelwidth\leftmarginvi
              \advance\labelwidth-\labelsep
              \parsep \z@ \itemsep \parsep}

%  -- end of inserted modified size10.clo

\setlength\lineskip{1\p@}
\setlength\normallineskip{1\p@}
\renewcommand\baselinestretch{1}
\setlength\parskip{0\p@}
\@lowpenalty   51
\@medpenalty  151
\@highpenalty 301
\setcounter{topnumber}{2}
\renewcommand\topfraction{.9}
\setcounter{bottomnumber}{2}
\renewcommand\bottomfraction{.9}
\setcounter{totalnumber}{3}
\renewcommand\textfraction{.1}
\renewcommand\floatpagefraction{.5}
\setcounter{dbltopnumber}{2}
\renewcommand\dbltopfraction{.9}
\renewcommand\dblfloatpagefraction{.5}
%\if@twoside
%  \def\ps@headings{%
%      \let\@oddfoot\@empty\let\@evenfoot\@empty
%      \def\@evenhead{\thepage\hfil\slshape\leftmark}%
%      \def\@oddhead{{\slshape\rightmark}\hfil\thepage}%
%      \let\@mkboth\markboth
%    \def\sectionmark##1{%
%      \markboth {\MakeUppercase{%
%        \ifnum \c@secnumdepth >\z@
%          \thesection\quad
%        \fi
%        ##1}}{}}%
%    \def\subsectionmark##1{%
%      \markright {%
%        \ifnum \c@secnumdepth >\@ne
%          \thesubsection\quad
%        \fi
%        ##1}}}
%\else
%  \def\ps@headings{%
%    \let\@oddfoot\@empty
%    \def\@oddhead{{\slshape\rightmark}\hfil\thepage}%
%    \let\@mkboth\markboth
%    \def\sectionmark##1{%
%      \markright {\MakeUppercase{%
%        \ifnum \c@secnumdepth >\m@ne
%          \thesection\quad
%        \fi
%        ##1}}}}
%\fi
%\def\ps@myheadings{%
%    \let\@oddfoot\@empty\let\@evenfoot\@empty
%    \def\@evenhead{\thepage\hfil\slshape\leftmark}%
%    \def\@oddhead{{\slshape\rightmark}\hfil\thepage}%
%    \let\@mkboth\@gobbletwo
%    \let\sectionmark\@gobble
%    \let\subsectionmark\@gobble
%}
%\if@titlepage
%  \newcommand\maketitle{\begin{titlepage}%
%  \let\footnotesize\small
%  \let\footnoterule\relax
%  \let \footnote \thanks
%  \null\vfil
%  \vskip 60\p@
%  \begin{center}%
%    {\LARGE \@title \par}%
%    \vskip 3em%
%    {\large
%     \lineskip .75em%
%      \begin{tabular}[t]{c}%
%        \@author
%      \end{tabular}\par}%
%      \vskip 1.5em%
%    {\large \@date \par}%       % Set date in \large size.
%  \end{center}\par
%  \@thanks
%  \vfil\null
%  \end{titlepage}%
%  \setcounter{footnote}{0}%
%  \global\let\thanks\relax
%  \global\let\maketitle\relax
%  \global\let\@thanks\@empty
%  \global\let\@author\@empty
%  \global\let\@date\@empty
%  \global\let\@title\@empty
%  \global\let\title\relax
%  \global\let\author\relax
%  \global\let\date\relax
%  \global\let\and\relax
%}
%\else
\newcommand\maketitle{\par
  \begingroup
%    \renewcommand\thefootnote{\@fnsymbol\c@footnote}%
%    The following breaks 1994 latex2e, so we use an older variant
%    \def\@makefnmark{\rlap{\@textsuperscript{\normalfont\@thefnmark}}}%
    \def\@makefnmark{\hbox to\z@{$\m@th^{\@thefnmark}$\hss}}%
%    \long\def\@makefntext##1{\parindent 1em\noindent
%            \hbox to1.8em{%
%                \hss\@textsuperscript{\normalfont\@thefnmark}}##1}%
    \if@twocolumn
%      \ifnum \col@number=\@ne
%        \@maketitle
%      \else
        \twocolumn[\@maketitle]%
%      \fi
    \else
      \newpage
      \global\@topnum\z@   % Prevents figures from going at top of page.
      \@maketitle
    \fi
    \thispagestyle{empty}\@thanks
  \endgroup
%  \setcounter{footnote}{0}%
  \global\let\thanks\relax
  \global\let\maketitle\relax
  \global\let\@maketitle\relax
  \global\let\@thanks\@empty
  \global\let\@author\@empty
  \global\let\@date\@empty
  \global\let\@title\@empty
  \global\let\title\relax
  \global\let\author\relax
  \global\let\date\relax
  \global\let\and\relax
}
\newcommand{\institute}[1]{\thanks{#1}}
\def\@maketitle{%
  \newpage
  \null
%  \vskip 2em%
  \begin{center}%
  \let \footnote \thanks
    {\tit@mysize\bfseries \@title \par}%
    \vskip 1.5em%
    {\aut@mysize\bfseries
%      \lineskip .5em%
      \begin{tabular}[t]{c}%
        \@author
      \end{tabular}\par}%
%    \vskip 1em%
%    {\large \@date}%
  \end{center}%
  \par
  \vskip 1.5em}
%\fi
\setcounter{secnumdepth}{3}
\newcounter {part}
\newcounter {section}
\newcounter {subsection}[section]
\newcounter {subsubsection}[subsection]
\newcounter {paragraph}[subsubsection]
\newcounter {subparagraph}[paragraph]
\renewcommand\thepart         {\@Roman\c@part}
\renewcommand\thesection      {\@arabic\c@section}
\renewcommand\thesubsection   {\thesection.\@arabic\c@subsection}
\renewcommand\thesubsubsection{\thesubsection .\@arabic\c@subsubsection}
\renewcommand\theparagraph    {\thesubsubsection.\@arabic\c@paragraph}
\renewcommand\thesubparagraph {\theparagraph.\@arabic\c@subparagraph}
\newcommand\part{\par
   \addvspace{4ex}%
   \@afterindentfalse
   \secdef\@part\@spart}

\def\@part[#1]#2{%
    \ifnum \c@secnumdepth >\m@ne
      \refstepcounter{part}%
      \addcontentsline{toc}{part}{\thepart\hspace{1em}#1}%
    \else
      \addcontentsline{toc}{part}{#1}%
    \fi
    {\parindent \z@ \raggedright
     \interlinepenalty \@M
     \normalfont
     \ifnum \c@secnumdepth >\m@ne
       \Large\bfseries \partname~\thepart
       \par\nobreak
     \fi
     \huge \bfseries #2%
     \markboth{}{}\par}%
    \nobreak
    \vskip 3ex
    \@afterheading}
\def\@spart#1{%
    {\parindent \z@ \raggedright
     \interlinepenalty \@M
     \normalfont
     \huge \bfseries #1\par}%
     \nobreak
     \vskip 3ex
     \@afterheading}
\newcommand\section{\@startsection {section}{1}{\z@}%
                                   {-16.5\p@ \@plus -5\p@ \@minus -3\p@}%
                                   {5.5\p@ \@plus5\p@}%
                                   {\normalfont\seca@mysize\bfseries\raggedright}}
\newcommand\subsection{\@startsection{subsection}{2}{\z@}%
                                   {-16.5\p@ \@plus -5\p@ \@minus -3\p@}%
                                   {5.5\p@ \@plus5\p@}%
                                   {\normalfont\secb@mysize\bfseries\raggedright}}
\newcommand\subsubsection{\@startsection{subsubsection}{3}{\z@}%
                                   {-16.5\p@ \@plus -5\p@ \@minus -3\p@}%
                                   {5.5\p@ \@plus5\p@}%
                                   {\normalfont\secc@mysize\itshape\raggedright}}
\newcommand\paragraph{\@startsection{paragraph}{4}{\z@}%
                                    {3.25ex \@plus1ex \@minus.2ex}%
                                    {-1em}%
                                    {\normalfont\normalsize\bfseries}}
\newcommand\subparagraph{\@startsection{subparagraph}{5}{\parindent}%
                                       {3.25ex \@plus1ex \@minus .2ex}%
                                       {-1em}%
                                      {\normalfont\normalsize\bfseries}}
\if@twocolumn
  \setlength\leftmargini  {10\p@}
\else
  \setlength\leftmargini  {2.5em}
\fi
\leftmargin  \leftmargini
\setlength\leftmarginii  {10\p@}
\setlength\leftmarginiii {5\p@}
\setlength\leftmarginiv  {5\p@}
\if@twocolumn
  \setlength\leftmarginv  {5\p@}
  \setlength\leftmarginvi {5\p@}
\else
  \setlength\leftmarginv  {1em}
  \setlength\leftmarginvi {1em}
\fi
\setlength  \labelsep  {5\p@}
\setlength  \labelwidth{\leftmargini}
\addtolength\labelwidth{-\labelsep}
\@beginparpenalty -\@lowpenalty
\@endparpenalty   -\@lowpenalty
\@itempenalty     -\@lowpenalty
\renewcommand\theenumi{\@arabic\c@enumi}
\renewcommand\theenumii{\@alph\c@enumii}
\renewcommand\theenumiii{\@roman\c@enumiii}
\renewcommand\theenumiv{\@Alph\c@enumiv}
\newcommand\labelenumi{\theenumi.}
\newcommand\labelenumii{(\theenumii)}
\newcommand\labelenumiii{\theenumiii.}
\newcommand\labelenumiv{\theenumiv.}
\renewcommand\p@enumii{\theenumi}
\renewcommand\p@enumiii{\theenumi(\theenumii)}
\renewcommand\p@enumiv{\p@enumiii\theenumiii}
\newcommand\labelitemi{$\m@th\bullet$}
\newcommand\labelitemii{\normalfont\bfseries --}
\newcommand\labelitemiii{$\m@th\ast$}
\newcommand\labelitemiv{$\m@th\cdot$}
\newenvironment{description}
               {\list{}{\labelwidth\z@ \itemindent-\leftmargin
                        \let\makelabel\descriptionlabel}}
               {\endlist}
\newcommand*\descriptionlabel[1]{\hspace\labelsep
                                \normalfont\bfseries #1}
%\if@titlepage
%  \newenvironment{abstract}{%
%      \titlepage
%      \null\vfil
%      \@beginparpenalty\@lowpenalty
%      \begin{center}%
%        \bfseries \abstractname
%        \@endparpenalty\@M
%      \end{center}}%
%     {\par\vfil\null\endtitlepage}
%\else
  \newenvironment{abstract}{%
      \if@twocolumn
        {\parindent 0mm\bf \abstractname.\hspace{3pt}}
%        \section*{\abstractname}%
      \else
        \small
        \begin{center}%
          {\bfseries \abstractname\vspace{-.5em}\vspace{\z@}}%
        \end{center}%
        \quotation
      \fi}
      {\if@twocolumn\else\endquotation\fi}
%\fi
\newenvironment{verse}
               {\let\\\@centercr
                \list{}{\itemsep      \z@
                        \itemindent   -1.5em%
                        \listparindent\itemindent
                        \rightmargin  \leftmargin
                        \advance\leftmargin 1.5em}%
                \item\relax}
               {\endlist}
\newenvironment{quotation}
               {\list{}{\listparindent 1.5em%
                        \itemindent    \listparindent
                        \rightmargin   \leftmargin
                        \parsep        \z@ \@plus\p@}%
                \item\relax}
               {\endlist}
\newenvironment{quote}
               {\list{}{\rightmargin\leftmargin}%
                \item\relax}
               {\endlist}
\if@compatibility
\newenvironment{titlepage}
    {%
      \if@twocolumn
        \@restonecoltrue\onecolumn
      \else
        \@restonecolfalse\newpage
      \fi
      \thispagestyle{empty}%
      \setcounter{page}\z@
    }%
    {\if@restonecol\twocolumn \else \newpage \fi
    }
\else
\newenvironment{titlepage}
    {%
      \if@twocolumn
        \@restonecoltrue\onecolumn
      \else
        \@restonecolfalse\newpage
      \fi
      \thispagestyle{empty}%
      \setcounter{page}\@ne
    }%
    {\if@restonecol\twocolumn \else \newpage \fi
     \if@twoside\else
        \setcounter{page}\@ne
     \fi
    }
\fi
\newcommand\appendix{\par
  \setcounter{section}{0}%
  \setcounter{subsection}{0}%
  \renewcommand\thesection{\@Alph\c@section}}
\setlength\arraycolsep{5\p@}
\setlength\tabcolsep{6\p@}
\setlength\arrayrulewidth{.4\p@}
\setlength\doublerulesep{2\p@}
\setlength\tabbingsep{\labelsep}
\skip\@mpfootins = \skip\footins
\setlength\fboxsep{3\p@}
\setlength\fboxrule{.4\p@}
\renewcommand\theequation{\@arabic\c@equation}
\newcounter{figure}
\renewcommand\thefigure{\@arabic\c@figure}
\def\fps@figure{htbp}
\def\ftype@figure{1}
\def\ext@figure{lof}
\def\fnum@figure{\figurename~\thefigure}
\newenvironment{figure}
               {\@float{figure}}
               {\end@float}
\newenvironment{figure*}
               {\@dblfloat{figure}}
               {\end@dblfloat}
\newcounter{table}
\renewcommand\thetable{\@arabic\c@table}
\def\fps@table{htbp}
\def\ftype@table{2}
\def\ext@table{lot}
\def\fnum@table{\tablename~\thetable}
\newenvironment{table}
               {\@float{table}\tabsize}
               {\end@float}
\newenvironment{table*}
               {\@dblfloat{table}}
               {\end@dblfloat}
\newlength\abovecaptionskip
\newlength\belowcaptionskip
\setlength\abovecaptionskip{6\p@}
\setlength\belowcaptionskip{2\p@}
\long\def\@makecaption#1#2{%
  \vskip\abovecaptionskip
  \sbox\@tempboxa{{\captsize{\bfseries #1.}\quad #2\normalsize}}%
  \ifdim \wd\@tempboxa >\hsize
    {\captsize{\bfseries #1.}\quad #2\normalsize}\par%
  \else
    \global \@minipagefalse
    \hbox to\hsize{\hfil\box\@tempboxa\hfil}%
  \fi
  \vskip\belowcaptionskip}
\DeclareOldFontCommand{\rm}{\normalfont\rmfamily}{\mathrm}
\DeclareOldFontCommand{\sf}{\normalfont\sffamily}{\mathsf}
\DeclareOldFontCommand{\tt}{\normalfont\ttfamily}{\mathtt}
\DeclareOldFontCommand{\bf}{\normalfont\bfseries}{\mathbf}
\DeclareOldFontCommand{\it}{\normalfont\itshape}{\mathit}
\DeclareOldFontCommand{\sl}{\normalfont\slshape}{\@nomath\sl}
\DeclareOldFontCommand{\sc}{\normalfont\scshape}{\@nomath\sc}
\DeclareRobustCommand*\cal{\@fontswitch\relax\mathcal}
\DeclareRobustCommand*\mit{\@fontswitch\relax\mathnormal}
\newcommand\@pnumwidth{1.55em}
\newcommand\@tocrmarg{2.55em}
\newcommand\@dotsep{4.5}
\setcounter{tocdepth}{3}
\newcommand\tableofcontents{%
    \section*{\contentsname
        \@mkboth{%
           \MakeUppercase\contentsname}{\MakeUppercase\contentsname}}%
    \@starttoc{toc}%
    }
\newcommand*\l@part[2]{%
  \ifnum \c@tocdepth >-2\relax
    \addpenalty\@secpenalty
    \addvspace{2.25em \@plus\p@}%
    \begingroup
      \setlength\@tempdima{3em}%
      \parindent \z@ \rightskip \@pnumwidth
      \parfillskip -\@pnumwidth
      {\leavevmode
       \large \bfseries #1\hfil \hbox to\@pnumwidth{\hss #2}}\par
       \nobreak
       \if@compatibility
         \global\@nobreaktrue
         \everypar{\global\@nobreakfalse\everypar{}}%
      \fi
    \endgroup
  \fi}
\newcommand*\l@section[2]{%
  \ifnum \c@tocdepth >\z@
    \addpenalty\@secpenalty
    \addvspace{1.0em \@plus\p@}%
    \setlength\@tempdima{1.5em}%
    \begingroup
      \parindent \z@ \rightskip \@pnumwidth
      \parfillskip -\@pnumwidth
      \leavevmode \bfseries
      \advance\leftskip\@tempdima
      \hskip -\leftskip
      #1\nobreak\hfil \nobreak\hbox to\@pnumwidth{\hss #2}\par
    \endgroup
  \fi}
\newcommand*\l@subsection{\@dottedtocline{2}{1.5em}{2.3em}}
\newcommand*\l@subsubsection{\@dottedtocline{3}{3.8em}{3.2em}}
\newcommand*\l@paragraph{\@dottedtocline{4}{7.0em}{4.1em}}
\newcommand*\l@subparagraph{\@dottedtocline{5}{10em}{5em}}
\newcommand\listoffigures{%
    \section*{\listfigurename
      \@mkboth{\MakeUppercase\listfigurename}%
              {\MakeUppercase\listfigurename}}%
    \@starttoc{lof}%
    }
\newcommand*\l@figure{\@dottedtocline{1}{1.5em}{2.3em}}
\newcommand\listoftables{%
    \section*{\listtablename
      \@mkboth{%
          \MakeUppercase\listtablename}{\MakeUppercase\listtablename}}%
    \@starttoc{lot}%
    }
\let\l@table\l@figure
\newdimen\bibindent
\setlength\bibindent{1.5em}
\newenvironment{thebibliography}[1]
     {\section*{\refname
        \@mkboth{\eightrm\MakeUppercase\refname}{\eightrm\MakeUppercase\refname}}%
      \refsize\list{[\@arabic\c@enumi]~}%
           {\settowidth\labelwidth{[0#1]~}%
            \leftmargin\labelwidth
%            \advance\leftmargin\labelsep
            \itemsep 0\p@
            \parsep 0\p@
            \@openbib@code
            \usecounter{enumi}%
            \let\p@enumi\@empty
            \renewcommand\theenumi{\@arabic\c@enumi}}%
      \sloppy\clubpenalty4000\widowpenalty4000\interlinepenalty=100%
      \sfcode`\.=1000}
     {\def\@noitemerr
       {\@latex@warning{Empty `thebibliography' environment}}%
      \endlist}
\newcommand\newblock{\hskip .11em\@plus.33em\@minus.07em}
\let\@openbib@code\@empty
\newenvironment{theindex}
               {\if@twocolumn
                  \@restonecolfalse
                \else
                  \@restonecoltrue
                \fi
                \columnseprule \z@
                \columnsep 35\p@
                \twocolumn[\section*{\indexname}]%
                \@mkboth{\MakeUppercase\indexname}%
                        {\MakeUppercase\indexname}%
                \thispagestyle{plain}\parindent\z@
                \parskip\z@ \@plus .3\p@\relax
                \let\item\@idxitem}
               {\if@restonecol\onecolumn\else\clearpage\fi}
\newcommand\@idxitem{\par\hangindent 40\p@}
\newcommand\subitem{\@idxitem \hspace*{20\p@}}
\newcommand\subsubitem{\@idxitem \hspace*{30\p@}}
\newcommand\indexspace{\par \vskip 10\p@ \@plus5\p@ \@minus3\p@\relax}
\count202=0
\renewcommand\footnoterule{%
  \global\advance\count202 1
  \kern-3\p@
  \hrule \@height 0.8\p@
  \kern 2.2\p@}
\newcommand\@makefntext[1]{%
    \ifnum\thefootnote<10\hangindent7pt\else\hangindent9pt\fi
    $^{\rm \@thefnmark}$ #1}
%    \parindent 1em%
%    \noindent
%    \hbox to1.8em{\hss\@makefnmark}#1}
\newcommand\contentsname{Contents}
\newcommand\listfigurename{List of Figures}
\newcommand\listtablename{List of Tables}
\newcommand\refname{REFERENCES}
\newcommand\indexname{Index}
\newcommand\figurename{Figure}
\newcommand\tablename{Table}
\newcommand\partname{Part}
\newcommand\appendixname{Appendix}
\newcommand\abstractname{Abstract}
\newcommand\today{}
\edef\today{\ifcase\month\or
  January\or February\or March\or April\or May\or June\or
  July\or August\or September\or October\or November\or December\fi
  \space\number\day, \number\year}
\setlength\columnsep{1.5pc}
\setlength\columnseprule{0\p@}
\setlength{\hoffset}{-3.5pc}
\pagestyle{plain}
\pagenumbering{arabic}
\frenchspacing
\if@twoside
\else
  \raggedbottom
\fi
\if@twocolumn
  \twocolumn
  \sloppy
  \flushbottom
\else
  \onecolumn
\fi

% -- now we add in the remaining bits of ecai96.sty that haven't already
%    been covered

\def\tit@mysize{\@setfontsize\tit@mysize\@xxpt{22}\bfseries}
\def\aut@mysize{\@setfontsize\aut@mysize\@xipt{12}}
\def\abs@mysize{\@setfontsize\abs@mysize\@viiipt{10}}
\def\seca@mysize{\@setfontsize\seca@mysize\@xipt{11}}
\def\secb@mysize{\@setfontsize\secb@mysize\@xipt{11}}
\def\secc@mysize{\@setfontsize\secc@mysize\@xpt{11}}
\def\footsize{\@setfontsize\footsize\@viiipt{9}}
\def\tabsize{\@setfontsize\tabsize\@viiipt{9}}
\def\captsize{\@setfontsize\captsize\@viiipt{9}}
\def\refsize{\@setfontsize\refsize\@viiipt{9}}
\def\progsize{\@setfontsize\progsize\@ixpt{10}}


\if@compatibility
    \@maxsep 20pt
    \@dblmaxsep 20pt
\fi

% for acknowledgements
\def\acknowledgements{\section*{\bf ACKNOWLEDGEMENTS}}
\def\ack{\acknowledgements}

\def\lquotation{\list{}{\listparindent 1.5em
 \setlength{\rightmargin}{1true cm}
 \setlength{\leftmargin}{\rightmargin}}\item[]}
\let\endlquotation=\endlist

\def\citestr#1{\nocite{#1}\csname b@#1\endcsname}

\def\and{{\enspace \rm and \enspace}}

\mark{{}{}}

\def\fnum@table{\captsize\bf Table \thetable}
\def\fnum@figure{\captsize\bf Figure \thefigure}

\long\def\@caption#1[#2]#3{\addcontentsline{\csname
  ext@#1\endcsname}{#1}{\protect\numberline{\csname
  the#1\endcsname}{\ignorespaces #2}}\par
  \begingroup
    \@parboxrestore
    \captsize
    \begin{center}
    \@makecaption{\csname fnum@#1\endcsname}{\ignorespaces #3}\par
    \end{center}
  \endgroup}

% support page numbers during submission phase
\gdef\@myfinalfoot{}
\def\ecaisubmission{%
\gdef\@myfinalfoot{\normalsize\hfill\thepage\hfill}
}

%section title
\def\sectionfoot#1{\gdef\@sectionfoot{#1}}

% author name
\def\authorfoot#1{\gdef\@authorfoot{#1}}

% defaults to empty footer for ECAI2004
% IOS will insert footers
\sectionfoot{}
\authorfoot{}

% Supply start page for each paper

\def\ecai#1{
\setcounter{page}{#1}
\gdef\@myauth{\footsize\copyright\ 2004 \@authorfoot}
\gdef\@myref{\footsize ECAI 2004. {\it 16th European Conference on
  Artificial Intelligence\/}}
\gdef\@myedit{\footsize Edited by Frank van Harmelen}
\gdef\@mycopyright{\footsize Published in 2004 by IOS Press}
}

%Set page counter to one by default
\ecai{1}
\newcounter{pageone}

\def\myfootnote{%
\vbox{\footnotesize
\hbox{\vrule height 0pt depth 0pt width0pt}
\ifodd\count202\relax\else\ifnum\thepageone=\thepage%
\hbox to \textwidth{\leaders\hrule height 0.8pt\hfill}%
\fi%
\fi
\hbox to \textwidth{\hfill}
\hbox to \textwidth{\noindent \@myauth\hfill}
\hbox to \textwidth{\noindent \@myref\hfill}
\hbox to \textwidth{\noindent \@myedit\hfill}
\hbox to \textwidth{\noindent \@mycopyright \hfill}}}

%***************************************
%Pagestyle to give correct page depth for second and subsequent pages
%***************************************
\def\ps@ecaifirst{\let\@mkboth\@gobbletwo%
     \def\@oddhead{}%
     \def\@oddfoot{\global\textheight\ntextheight}%
     \def\@evenhead{}%
     \let\@evenfoot\@oddfoot}
\let\ps@empty\ps@ecaifirst
\let\ps@plain\ps@ecaifirst
\ps@empty

\def\ps@ecai{\let\@mkboth\@gobbletwo%
     \def\@oddfoot{\@myfinalfoot}
     \let\@evenfoot\@oddfoot
     \def\@oddhead{}
     \let\@evenhead\@oddhead}

\pagestyle{ecai}

\thispagestyle{ecaifirst}
\textheight\ftextheight

\newtheorem{theorem}{Theorem}

%List within theorem
\newcounter{theoremlistno}
\newenvironment{theoremlist}{%
\begin{list}{\arabic{theoremlistno}.}{\usecounter{theoremlistno}
  \setlength{\leftmargin}{10pt}
  \setlength{\labelsep}{6pt}
  \setlength{\labelwidth}{6pt}
  \sl}}
{\end{list}}

\endinput
