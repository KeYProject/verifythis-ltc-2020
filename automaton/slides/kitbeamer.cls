\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{kitbeamer}[2020-11-16 v3.0 SDQ Beamer class]

\newif\ifsectionnavigation
\newif\ifnavbarinfoot
\newif\ifnavbarinline
\newif\ifnavbarside
\newif\iffourtothree
\newif\ifsixteentonine
\newif\ifsixteentoten
\newif\ifgerman
\newif\ifsmallfooterfont

\def\kitslogan#1{\def\@kitslogan{#1}}
\def\kitlogo#1{\def\@kitlogo{#1}}
\def\groupname#1{\def\@groupname{#1}}

% siehe README.md
\DeclareOption{de}{
  \kitslogan{KIT -- Die Forschungsuniversität in der Helmholtz-Gemeinschaft}
  \kitlogo{kitlogo_de_rgb}
  \germantrue
  \PassOptionsToPackage{autostyle}{csquotes}
  }
\DeclareOption{en}{
  \kitslogan{KIT -- The Research University in the Helmholtz Association}
  \kitlogo{kitlogo_en_rgb}
  \germanfalse
  }
\DeclareOption{4:3}{
  \fourtothreetrue
  \sixteentoninefalse
  \sixteentotenfalse
}
\DeclareOption{16:9}{
	\fourtothreefalse
	\sixteentoninetrue
	\sixteentotenfalse
}
\DeclareOption{16:10}{
	\fourtothreefalse
	\sixteentoninefalse
	\sixteentotentrue
}
\DeclareOption{navbarside}{
  \sectionnavigationtrue
  \navbarsidetrue
  \navbarinlinefalse
  \navbarinfootfalse
}
\DeclareOption{navbarinline}{
  \sectionnavigationtrue
  \navbarsidefalse
  \navbarinlinetrue
  \navbarinfootfalse
}
\DeclareOption{navbarinfooter}{
  \sectionnavigationtrue
  \navbarsidefalse
  \navbarinlinefalse
  \navbarinfoottrue
}
\DeclareOption{navbaroff}{
  \sectionnavigationfalse
}
\DeclareOption{navbarkit}{
  \sectionnavigationfalse
  \smallfooterfonttrue
}
\DeclareOption{smallfoot}{
  \smallfooterfonttrue
}
\DeclareOption{bigfoot}{
  \smallfooterfontfalse
}

\ExecuteOptions{de,16:9,navbarinline,bigfoot}

\DeclareOption*{\PassOptionsToClass{\CurrentOption}{beamer}}

\ProcessOptions\relax

\LoadClass[10pt,utf8]{beamer}

% Babel-Paket wird nur bei deutscher Sprache benötigt
\ifgerman
  \RequirePackage[ngerman]{babel}
\fi
\RequirePackage{csquotes}
\RequirePackage{hyperref}
\RequirePackage[absolute,overlay]{textpos}

%% ---------------
%% | Typographie |
%% ---------------

\RequirePackage[utf8]{inputenc}
\RequirePackage[T1]{fontenc}

\RequirePackage{microtype}

\RequirePackage[scaled=.92]{helvet}
\RequirePackage[scaled=.78]{beramono}
\RequirePackage{libertineRoman}
\RequirePackage[libertine]{newtxmath}

\setbeamerfont{title}{series=\bfseries,size=\Large}
\setbeamerfont{frametitle}{series=\bfseries,size=\Large}

%% -----------------
%% | Folien-Layout |
%% -----------------

% Seitenverhältnis
%
% Die Folien sind auf die Standardhöhe in LaTeX Beamer (9,6 cm) normiert.
% Die Maße der KIT-Gestaltungsrichtlinien (Folienhöhe 14,3 cm) wurden durch
% den Quotienten 1,5 geteilt.

\RequirePackage{geometry}
\iffourtothree
	\geometry{papersize={12.8cm,9.6cm}}
\fi
\ifsixteentoten
	\geometry{papersize={15.36cm,9.6cm}}
\fi
\ifsixteentonine
	\geometry{papersize={17.07cm,9.6cm}}
\fi

% Ränder laut Gestaltungsrichtlinen; 3 mm -> 2 mm, 11 mm -> 7,3 mm
\newlength{\kitoutermargin}
\setlength{\kitoutermargin}{2mm}
\newlength{\kitinnermargin}
\setlength{\kitinnermargin}{7.3mm}
\newlength{\kitbottommargin}
\setlength{\kitbottommargin}{\kitinnermargin}

% Ränder außen
\setbeamersize{text margin left=\kitinnermargin,text margin right=\kitinnermargin} 

% keine Navigationssymbole
\setbeamertemplate{navigation symbols}{}
\setbeamercovered{invisible}
\useinnertheme{rounded}

% Folientitel
\setbeamertemplate{frametitle}{
  \ifbeamer@plainframe\else%
    % Unterkante Titeltext: 22,5 mm -> 15 mm von Seitenkopf
    \begin{textblock*}{\dimexpr\paperwidth-30mm}[0,1](\kitinnermargin,15mm)%
      \usebeamerfont{frametitle}\insertframetitle%
    \end{textblock*}%
    \begin{textblock*}{20mm}[1,1](\dimexpr\paperwidth-\kitinnermargin\relax,15mm)%j
        \includegraphics[width=20mm]{logos/\@kitlogo}%
    \end{textblock*}%
  \fi
% Rand oben (ergibt Beginn des Textes bei 34 mm -> 22,7 mm)
  \vspace {18mm}
}

%% Fußzeile
\newlength{\kitbottom}
  % Navbar in Footer: Schmale Fußzeile
\ifnavbarinfoot
  % Bei Navbar in Footer immer kleiner Font in der Fußzeile
  \setbeamerfont{footer}{size=\fontsize{6pt}{7.2pt}\selectfont}
  \setlength{\kitbottom}{4mm}
\else
  % Ansonsten kleiner Text nur, wenn "smallfoot" gewählt
  \ifsmallfooterfont
    \setbeamerfont{footer}{size=\fontsize{6pt}{7.2pt}\selectfont}
  \else
    \setbeamerfont{footer}{size=\scriptsize}
  \fi
  \setlength{\kitbottom}{\kitbottommargin}
\fi
\setbeamerfont{page number in head/foot}{series=\bfseries}

\newlength{\kitbottomdepth}
\newlength{\kitbottomheight}
\newlength{\kitfootergroupwidth}

\setbeamertemplate{footline}{%
\setlength{\kitbottomdepth}{\dimexpr.5\kitbottom-.5em\relax}%
\setlength{\kitbottomheight}{\dimexpr.5\kitbottom+.5em\relax}%
  %% die "%" am Ende sind nötig, damit keine Abstände eingefügt werden
  %
  % Falls kein Gruppenname angegeben, die ganze Breite der Fußzeile für den Titel nutzen.
  \ifdefined\@groupname%
    \ifx\@groupname\empty%
      \setlength{\kitfootergroupwidth}{0mm}%
      \else%
      \setlength{\kitfootergroupwidth}{50mm}%
    \fi%
  \else
      \setlength{\kitfootergroupwidth}{0mm}%
  \fi
  \usebeamerfont{footer}%
  \ifsectionnavigation%
    % Option "navbarinline"
    \ifnavbarinline%
      \begin{beamercolorbox}[wd=\paperwidth, leftskip=2mm, rightskip=2mm]{}
        \insertnavigation{\dimexpr\paperwidth-4mm\relax}
        \vspace{1mm}
      \end{beamercolorbox}%
    \fi%
    % Option "navbarinfooter"
    \ifnavbarinfoot%
      % Punkte für Subsections deaktivieren
      \setbeamertemplate{mini frames}{}%
      \begin{beamercolorbox}[wd=\paperwidth, leftskip=1mm, rightskip=1mm]{}%
        \insertsectionnavigationhorizontal{\dimexpr\paperwidth-\kitoutermargin\relax}{}{}
      \end{beamercolorbox}%
    \fi%
  \fi%
  \leavevmode%
  \begin{beamercolorbox}[wd=13mm, ht=\kitbottomheight, dp=\kitbottomdepth, leftskip=4mm]{}
      \usebeamerfont{page number in head/foot}%
      \strut\insertframenumber{}/\inserttotalframenumber%
  \end{beamercolorbox}%
  \begin{beamercolorbox}[wd=20mm, ht=\kitbottomheight, dp=\kitbottomdepth]{}
      \usebeamerfont{date in head/foot}%
      \strut\insertshortdate%
  \end{beamercolorbox}%
  \begin{beamercolorbox}[wd=\dimexpr\paperwidth-37mm-\kitfootergroupwidth, ht=\kitbottomheight, dp=\kitbottomdepth]{}%
      \beamer@shortauthor: \beamer@shorttitle%
  \end{beamercolorbox}%
  \ifdefined\@groupname%
  \begin{beamercolorbox}[wd=\kitfootergroupwidth, ht=\kitbottomheight, dp=\kitbottomdepth, rightskip=\kitinnermargin]{}
    \raggedleft\@groupname
  \end{beamercolorbox}%
  \fi% 
}

%% Option "navbarside"
\ifnavbarside
\useoutertheme[height=0cm,width=3.5cm,left]{sidebar}

\setbeamerfont{title in sidebar}{family=\sffamily,series=\mdseries,size={\fontsize{10pt}{11pt}}}
\setbeamerfont{section in sidebar}{family=\sffamily,series=\mdseries,size={\fontsize{9pt}{9.9pt}}}
\setbeamerfont{subsection in sidebar}{family=\sffamily,series=\mdseries,size={\fontsize{8pt}{8.8pt}}}

\setbeamertemplate{sidebar \beamer@sidebarside}
  {\vskip1.5cm%
   \hskip6.5mm%
   \advance\beamer@sidebarwidth by -5mm%
   \insertverticalnavigation{\beamer@sidebarwidth}%
  }%
\fi

%% Hintergrund
\usebackgroundtemplate{
  % Trennlinie nicht bei "plain"-Frames
  \ifbeamer@plainframe\else\kitseparationline\fi
}

% Trennlinie
\newcommand{\kitseparationline}{
  \begin{pgfpicture}{0mm}{0mm}{\paperwidth}{\paperheight}
    \pgfsetstrokecolor{black!15} 
    \pgfsetlinewidth{.5pt}
    \pgfpathmoveto{\pgfpoint{\kitoutermargin}{\kitinnermargin}}
    \pgfpathlineto{\pgfpoint{\paperwidth-\kitoutermargin}{\kitinnermargin}}
    \pgfusepath{stroke} 
  \end{pgfpicture}%
}


%% --------------
%% | Titelseite |
%% --------------

\def\titleimage#1{\def\@titleimage{#1}}
\def\grouplogo#1{\def\@grouplogo{#1}}

\newcommand{\KITtitleframe}{
  \begin{frame}[plain]
  \titlepage
  \end{frame}
}

\setbeamertemplate{title page}{
  % From textpos documentation (https://ctan.org/pkg/textpos)
  %
  % \begin{textblock}{<hsize>}[<ho>,<vo>](<hpos>,<vpos>)
  %   The coordinates <ho> and <vo> are fractions of the width and height of the text
  %   box, respectively, and state that the box is to be placed so that the reference point
  %   (<ho>,<vo>) within the box is to be placed at the point (<hpos>,<vpos>) on the page.

  % KIT-Logo
  \begin{textblock*}{30mm}(\kitinnermargin,6.7mm)
  \includegraphics[width=30mm]{logos/\@kitlogo} 
  \end{textblock*}
  
  % Gruppenlogo
  \ifdefined\@grouplogo
    \ifx\@grouplogo\empty \else
      \begin{textblock*}{20mm}(\dimexpr\paperwidth-24mm\relax,6.7mm)
      \includegraphics[width=20mm,height=20mm,keepaspectratio]{logos/\@grouplogo} 
      \end{textblock*}
    \fi % falls \grouplogo{} aufgerufen wird, kein Gruppenlogo einbinden
    \else
      \begin{textblock*}{20mm}(\dimexpr\paperwidth-24mm\relax,6.7mm)
      \colorbox{kit-lila100!20}{\parbox[t][12mm][c]{19mm}{\color{kit-lila100}\scriptsize\centering Bitte Logo über \texttt{\textbackslash grouplogo\{\}} festlegen.}}
      \end{textblock*}
  \fi 
  
  % Titel
  \begin{textblock*}{\dimexpr\paperwidth-8mm\relax}[0,.5](\kitinnermargin,28mm)
  \usebeamerfont*{title}\inserttitle
  \end{textblock*}
  
  % Untertitel
  \begin{textblock*}{\dimexpr\paperwidth-8mm\relax}(\kitinnermargin,36mm)
  \small\textbf{\insertsubtitle}
  \end{textblock*}
  
  % Autor
  \begin{textblock*}{\dimexpr\paperwidth-8mm\relax}(\kitinnermargin,41mm)
  \small\insertauthor~\textbar~\insertdate
  \end{textblock*}

  % Titelbild
  \newlength{\kittitleimageheight}
  \setlength{\kittitleimageheight}{40mm}
  \begin{textblock*}{\paperwidth}(\kitoutermargin,\dimexpr\paperheight-\kitbottommargin-\kittitleimageheight)
  \begin{pgfpicture}{0mm}{0mm}{\paperwidth}{\kittitleimageheight}
    % Clipping-Pfad um titelbild
    \pgfsetstrokecolor{black!15} 
    \pgfsetlinewidth{1pt}
    \pgfsetcornersarced{\pgfpoint{3mm}{3mm}}
    \pgfpathmoveto{\pgfpoint{\paperwidth-2\kitoutermargin}{0mm}}
    \pgfpathlineto{\pgfpoint{\paperwidth-2\kitoutermargin}{\kittitleimageheight}}
    \pgfsetcornersarced{\pgfpointorigin}
    \pgfpathlineto{\pgfpoint{0mm}{\kittitleimageheight}}
    \pgfsetcornersarced{\pgfpoint{3mm}{3mm}}
    \pgfpathlineto{\pgfpointorigin}
    \pgfsetcornersarced{\pgfpointorigin}
    \pgfpathclose
    \pgfusepath{stroke,clip} 
    
    % Titelbild
    \ifdefined\@titleimage
      \ifx\@groupname\empty \else%
        \pgftext[at=\pgfpoint{.5\paperwidth}{0mm},center,bottom]{%
          \includegraphics[height=40mm]{logos/\@titleimage}
        }
        \fi % Bei Aufruf von \titleimage{} leeren Rahmen anzeigen.
      \else 
        \pgftext[at=\pgfpoint{.5\paperwidth}{.5\kittitleimageheight},center,base]{%
          \colorbox{kit-lila100!20}{\parbox[c][\kittitleimageheight][c]{\paperwidth}{\color{kit-lila100}\centering Bitte Titelbild über \texttt{\textbackslash titleimage\{\}} festlegen.
          }}%
        }
    \fi
    

  \end{pgfpicture}%
  \end{textblock*}

  
  % KIT slogan
  \begin{textblock*}{80mm}[0,.5](\kitoutermargin,\dimexpr\paperheight-.5\kitbottommargin)
      \fontsize{5.5pt}{5.5pt}\selectfont\@kitslogan
  \end{textblock*}
  
  \begin{textblock*}{30mm}[1,.5](\dimexpr\paperwidth-\kitoutermargin\relax,\dimexpr\paperheight-.5\kitbottommargin)
      \fontsize{11pt}{11pt}\selectfont\bfseries\raggedleft%
      {\href{https://www.kit.edu}{www.kit.edu}}
  \end{textblock*}
  
}
%% ---------------
%% | /Titelseite |
%% ---------------

%% ----------
%% | Farben |
%% ----------
%% KIT-Farbschema

\definecolor{kit-green100}{rgb}{0,.59,.51}
\definecolor{kit-green70}{rgb}{.3,.71,.65}
\definecolor{kit-green50}{rgb}{.50,.79,.75}
\definecolor{kit-green30}{rgb}{.69,.87,.85}
\definecolor{kit-green15}{rgb}{.85,.93,.93}

\definecolor{kit-blue100}{rgb}{.27,.39,.67}
\definecolor{kit-blue70}{rgb}{.49,.57,.76}
\definecolor{kit-blue50}{rgb}{.64,.69,.83}
\definecolor{kit-blue30}{rgb}{.78,.82,.9}
\definecolor{kit-blue15}{rgb}{.89,.91,.95}

\definecolor{kit-yellow100}{cmyk}{0,.05,1,0}
\definecolor{kit-yellow70}{cmyk}{0,.035,.7,0}
\definecolor{kit-yellow50}{cmyk}{0,.025,.5,0}
\definecolor{kit-yellow30}{cmyk}{0,.015,.3,0}
\definecolor{kit-yellow15}{cmyk}{0,.0075,.15,0}

\definecolor{kit-orange100}{cmyk}{0,.45,1,0}
\definecolor{kit-orange70}{cmyk}{0,.315,.7,0}
\definecolor{kit-orange50}{cmyk}{0,.225,.5,0}
\definecolor{kit-orange30}{cmyk}{0,.135,.3,0}
\definecolor{kit-orange15}{cmyk}{0,.0675,.15,0}

\definecolor{kit-red100}{cmyk}{.25,1,1,0}
\definecolor{kit-red70}{cmyk}{.175,.7,.7,0}
\definecolor{kit-red50}{cmyk}{.125,.5,.5,0}
\definecolor{kit-red30}{cmyk}{.075,.3,.3,0}
\definecolor{kit-red15}{cmyk}{.0375,.15,.15,0}

\definecolor{kit-lila100}{rgb}{.64,.06,.49}

\definecolor{kit-brown100}{rgb}{.65,.51,.18}

\definecolor{kit-cyan100}{rgb}{.03,.62,.87}

\definecolor{kit-maygreen100}{rgb}{.47,.64,0}

\setbeamercolor*{normal text}{fg=black}
\setbeamercolor*{alerted text}{fg=kit-red100}
\setbeamercolor*{example text}{fg=black}
\setbeamercolor*{structure}{fg=black}

\setbeamercolor*{palette primary}{fg=black,bg=black!15}
\setbeamercolor*{palette secondary}{fg=black,bg=black!15}
\setbeamercolor*{palette tertiary}{fg=black,bg=black!15}
\setbeamercolor*{palette quaternary}{fg=black,bg=black!15}

\setbeamercolor*{palette sidebar primary}{fg=black!75}
\setbeamercolor*{palette sidebar secondary}{fg=black!75}
\setbeamercolor*{palette sidebar tertiary}{fg=black!75}
\setbeamercolor*{palette sidebar quaternary}{fg=black!75}

\setbeamercolor*{item projected}{fg=white,bg=kit-green100}

\setbeamercolor*{block title}{fg=white,bg=kit-green100}
\setbeamercolor*{block title alerted}{use=alerted text,fg=white,bg=alerted text.fg!75!black}
\setbeamercolor*{block title example}{fg=white,bg=kit-blue100}

\setbeamercolor*{block body}{fg=black,bg=kit-green15}
\setbeamercolor*{block body alerted}{parent=normal text,use=block title alerted,bg=block title alerted.bg!10!bg}
\setbeamercolor*{block body example}{fg=black,bg=kit-blue15}

\setbeamercolor*{separation line}{}
\setbeamercolor*{fine separation line}{}

\setbeamercolor*{background canvas}{bg=white}

%% -----------
%% | /Farben |
%% -----------

%% -----------------------------------
%% | halbgerundete Aufzählungspunkte |
%% -----------------------------------

\setbeamertemplate{itemize items}{
  \raisebox{.25ex}{
    \begin{pgfpicture}{0mm}{0mm}{1ex}{1ex}
    {\pgfsetcornersarced{\pgfpoint{.3ex}{.3ex}} 
    \pgfpathmoveto{\pgfpoint{0cm}{1ex}} 
    \pgfpathlineto{\pgfpoint{1ex}{1ex}}
    \pgfpathlineto{\pgfpoint{1ex}{0cm}}}
    {\pgfsetcornersarced{\pgfpoint{.3ex}{.3ex}}
    \pgfpathmoveto{\pgfpoint{1ex}{0cm}}
    \pgfpathlineto{\pgfpointorigin}
    \pgfpathlineto{\pgfpoint{0cm}{1ex}}}
    \color{kit-green100}
    \pgfusepath{fill}
    \end{pgfpicture}%
  }
}

%% ------------------------------
%% | halbgerundete Beamer-Boxen |
%% ------------------------------

\renewcommand\beamerboxesrounded[2][]{%
  \global\let\beamer@firstlineitemizeunskip=\relax%
  \vbox\bgroup%
  \setkeys{beamerboxes}{upper=block title,lower=block body,width=\textwidth,shadow=false}%
  \setkeys{beamerboxes}{#1}%
  {%
    \usebeamercolor{\bmb@lower}%
    \globalcolorstrue%
    \colorlet{lower.bg}{bg}%
  }%
  {%
    \usebeamercolor{\bmb@upper}%
    \globalcolorstrue%
    \colorlet{upper.bg}{bg}%
  }%
  %
  % Typeset head
  %
  \vskip4bp
  \setbox\bmb@box=\hbox{%
    \begin{minipage}[b]{\bmb@width}%
      \usebeamercolor[fg]{\bmb@upper}%
      #2%
    \end{minipage}}%
  \ifdim\wd\bmb@box=0pt%
    \setbox\bmb@box=\hbox{}%
    \ht\bmb@box=1.5pt%
    \bmb@prevheight=-4.5pt%
  \else%
    \wd\bmb@box=\bmb@width%
    \bmb@temp=\dp\bmb@box%
    \ifdim\bmb@temp<1.5pt%
      \bmb@temp=1.5pt%
    \fi%
    \setbox\bmb@box=\hbox{\raise\bmb@temp\hbox{\box\bmb@box}}%
    \dp\bmb@box=0pt%
    \bmb@prevheight=\ht\bmb@box%
  \fi%
  \bmb@temp=\bmb@width%
  \bmb@dima=\bmb@temp\advance\bmb@dima by2.2bp%
  \bmb@dimb=\bmb@temp\advance\bmb@dimb by4bp%
  \hbox{%
    \begin{pgfpicture}{0bp}{+-\ht\bmb@box}{0bp}{+-\ht\bmb@box}
      \ifdim\wd\bmb@box=0pt%
        \color{lower.bg}%
      \else%        
        \color{upper.bg}%
      \fi%  
      \pgfpathqmoveto{-4bp}{-1bp}
      % Adaption for "KIT-Design"
      \pgfpathlineto{\pgfpoint{-4bp}{3bp}}
      %\pgfpathqcurveto{-4bp}{1.2bp}{-2.2bp}{3bp}{0bp}{3bp}
      \pgfpathlineto{\pgfpoint{\bmb@temp}{3bp}}
      \pgfpathcurveto%
      {\pgfpoint{\bmb@dima}{3bp}}%
      {\pgfpoint{\bmb@dimb}{1.2bp}}%
      {\pgfpoint{\bmb@dimb}{-1bp}}%
      \bmb@dima=-\ht\bmb@box%
      \advance\bmb@dima by-2pt%
      \pgfpathlineto{\pgfpoint{\bmb@dimb}{\bmb@dima}}
      \pgfpathlineto{\pgfpoint{-4bp}{\bmb@dima}}
      \pgfusepath{fill}
    \end{pgfpicture}%
    \copy\bmb@box%
  }%
  \nointerlineskip%
  \vskip-1pt%
  \ifdim\wd\bmb@box=0pt%
  \else%
  \hbox{%
    \begin{pgfpicture}{0pt}{0pt}{\bmb@width}{6pt}
      \bmb@dima=\bmb@width%
      \advance\bmb@dima by8bp%
      \pgfpathrectangle{\pgfpoint{-4bp}{-1bp}}{\pgfpoint{\bmb@dima}{8bp}}
      \pgfusepath{clip}
      {\pgftransformshift{\pgfpoint{-4bp}{0bp}}\pgftext[left,base]{\pgfuseshading{bmb@transition}}}%
    \end{pgfpicture}%
  }%
  \nointerlineskip%
  \vskip-0.5pt%
  \fi%
  \ifbmb@shadow%
    \setbox\bmb@boxshadow=\hbox{\pgfuseshading{bmb@shadow}}%
    \setbox\bmb@boxshadowball=\hbox{\pgfuseshading{bmb@shadowball}}%
    \setbox\bmb@boxshadowballlarge=\hbox{\pgfuseshading{bmb@shadowballlarge}}%
  \fi%
  \setbox\bmb@colorbox=\hbox{{\pgfpicturetrue\pgfsetcolor{lower.bg}}}%
  \setbox\bmb@box=\hbox\bgroup\begin{minipage}[b]{\bmb@width}%
    \vskip2pt%
    \usebeamercolor[fg]{\bmb@lower}%
    \colorlet{beamerstructure}{upper.bg}%
    \colorlet{structure}{upper.bg}%
    %\color{.}%
  }

\def\endbeamerboxesrounded{%
  \end{minipage}\egroup%
  \wd\bmb@box=\bmb@width%
  \bmb@temp=\dp\bmb@box%
  \advance\bmb@temp by.5pt%
  \setbox\bmb@box=\hbox{\raise\bmb@temp\hbox{\box\bmb@box}}%
  \dp\bmb@box=0pt%
  \bmb@temp=\wd\bmb@box%
  \bmb@dima=\bmb@temp\advance\bmb@dima by2.2bp%
  \bmb@dimb=\bmb@temp\advance\bmb@dimb by4bp%
  \hbox{%
    \begin{pgfpicture}{0bp}{0bp}{0bp}{0bp}
      \ifbmb@shadow%
      {\pgftransformshift{\pgfpoint{4bp}{-3bp}}\pgftext{\copy\bmb@boxshadowball}}
      \begin{pgfscope}
        {%
        \advance\bmb@temp by-1bp%
        \pgfpathrectangle{\pgfpoint{\bmb@temp}{-7bp}}{\pgfpoint{9bp}{9bp}}%
        \pgfusepath{clip}
        }%
        {\pgftransformshift{\pgfpoint{\bmb@temp}{1bp}}\pgftext{\box\bmb@boxshadowballlarge}}
      \end{pgfscope}
      \begin{pgfscope}
        \advance\bmb@temp by-4bp%
        \pgfpathrectangle{\pgfpoint{4bp}{-7bp}}{\pgfpoint{\bmb@temp}{5bp}}
        \pgfusepath{clip}
        {\pgftransformshift{\pgfpoint{4bp}{-7bp}}\pgftext[left,base]{\copy\bmb@boxshadow}}%
      \end{pgfscope}
      \begin{pgfscope}
        \advance\bmb@temp by 4bp%
        \bmb@dima=\ht\bmb@box%
        \advance\bmb@dima by\bmb@prevheight%
        \advance\bmb@dima by 4bp%
        \pgfpathrectangle{\pgfpoint{\bmb@temp}{1bp}}{\pgfpoint{4bp}{\bmb@dima}}
        \pgfusepath{clip}
        \advance\bmb@dima by-4bp%
        {\pgftransformshift{\pgfpoint{\bmb@temp}{\bmb@dima}}\pgftext{\box\bmb@boxshadowball}}
        \advance\bmb@dima by-1bp%
        \pgfpathrectangle{\pgfpoint{\bmb@temp}{1bp}}{\pgfpoint{4bp}{\bmb@dima}}
        \pgfusepath{clip}
        \advance\bmb@temp by4bp%
        {\pgftransformshift{\pgfpoint{\bmb@temp}{-3bp}}%
          \pgftransformrotate{90}%
          \pgftext[left,base]{\box\bmb@boxshadow}}%
      \end{pgfscope}
      \fi%
      \unhbox\bmb@colorbox%
      \pgfpathqmoveto{-4bp}{1bp}
      \pgfpathqcurveto{-4bp}{-1.2bp}{-2.2bp}{-3bp}{0bp}{-3bp}
      \pgfpathlineto{\pgfpoint{\the\bmb@dimb}{-3bp}}
      {
      \bmb@dima=\ht\bmb@box%
      \pgfpathlineto{\pgfpoint{\bmb@dimb}{\bmb@dima}}
      \pgfpathlineto{\pgfpoint{-4bp}{\bmb@dima}}
      \pgfusepath{fill}
      }
      \ifbmb@shadow%
      {
        \color{black!50!bg}
        \pgfsetlinewidth{0pt}
        \pgfpathmoveto{\pgfpoint{\bmb@dimb}{-.5bp}}
        \bmb@dima=\ht\bmb@box%
        \advance\bmb@dima by\bmb@prevheight%
        \advance\bmb@dima by 1bp%
        \pgfpathlineto{\pgfpoint{\bmb@dimb}{\bmb@dima}}
        \pgfusepath{stroke}
        \bmb@temp=\bmb@dima
        \advance\bmb@dima by 1bp%
        \color{black!31!bg}
        \pgfpathmoveto{\pgfpoint{\bmb@dimb}{\bmb@temp}}
        \pgfpathlineto{\pgfpoint{\bmb@dimb}{\bmb@dima}}
        \pgfusepath{stroke}
        \advance\bmb@dima by 1bp%
        \advance\bmb@temp by 1bp%
        \color{black!19!bg}
        \pgfpathmoveto{\pgfpoint{\bmb@dimb}{\bmb@temp}}
        \pgfpathlineto{\pgfpoint{\bmb@dimb}{\bmb@dima}}
        \pgfusepath{stroke}
        \advance\bmb@dima by 1bp%
        \advance\bmb@temp by 1bp%
        \color{black!6!bg}
        \pgfpathmoveto{\pgfpoint{\bmb@dimb}{\bmb@temp}}
        \pgfpathlineto{\pgfpoint{\bmb@dimb}{\bmb@dima}}
        \pgfusepath{stroke}
        \advance\bmb@dima by 1.5bp%
        \advance\bmb@temp by 1bp%
        \color{bg}
        \pgfpathmoveto{\pgfpoint{\bmb@dimb}{\bmb@temp}}
        \pgfpathlineto{\pgfpoint{\bmb@dimb}{\bmb@dima}}
        \pgfusepath{stroke}
      }
      \fi
    \end{pgfpicture}%
    \box\bmb@box%
  }%
  \ifbmb@shadow%
    \vskip4bp minus 2bp%
  \else%
    \vskip2bp%
  \fi%
  \egroup% of \vbox\bgroup
}

%% ----------------------------------------
%% | /KIT-style semi-rounded beamer boxes |
%% ----------------------------------------

%% -----------------
%% | Backup-Folien |
%% -----------------
\newcommand{\beginbackup}{
   \newcounter{framenumbervorappendix}
   \setcounter{framenumbervorappendix}{\value{framenumber}}
}
\newcommand{\backupend}{
   \addtocounter{framenumbervorappendix}{-\value{framenumber}}
   \addtocounter{framenumber}{\value{framenumbervorappendix}} 
}
%% ------------------
%% | /Backup-Folien |
%% ------------------