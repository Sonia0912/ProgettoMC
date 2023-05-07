(* ::Package:: *)

(* :Title: Esercizio Analisi Sintattica *)
(* :Context: AnalisiSintattica` *)
(* :Author: Lorenzo Campidelli, Luca Castricini, Gianluca Gueli, Sonia Nicoletti, Anna Tosoroni *)
(* :Summary: Pacchetto che permette la generazioni di esercizi sull'analisi sintattica *)
(* :Copyright: GS 2023 *)
(* :Package Version: 1 *)
(* :Mathematica Version: 13 *)
(* :History: last modified 07/05/2023 *)
(* :Keywords: analisi sintattica, compilatori, interpreti, grammatica *)
(* :Sources: biblio *)
(* :Limitations: this is a preliminary version, for educational purposes only. *)
(* :Discussion: *)
(* :Requirements: *)
(* :Warning: DOCUMENTARE TUTTO il codice *)


BeginPackage["AnalisiSintattica`"]


GenerazioneGrammatica::usage =
"GenerazioneGrammatica[] genera le regole della grammatica per l'esercizio."


Begin["`Private`"]


(*GENERAZIONE GRAMMATICA CASUALE*)
(*
- A ogni Non Terminale (sempre 4) e' associata una lista di 1-3 Terminali e 2-3 Non Terminali (almeno 1 deve essere il Non Terminale successivo nella lista - tranne per l'ultimo Non Terminale, che ha solo Terminali)
- Tutti gli elementi della lista devono apparire esattamente una volta nelle produzioni (1-4 produzioni) 
- Esempio:
A: a, b, B, C
B: c, d, C
C: e, f, D
D: g, h
*)

(*Parametri*)
tuttiNonTerminali = CharacterRange["A","D"];
tuttiTerminali = CharacterRange["a","l"];

nonTerminali = tuttiNonTerminali;
terminali = tuttiTerminali;

numNonTerminali = Length[nonTerminali];
numTerminali = Length[terminali];

minNumeroNonTerminali = 1;
maxNumeroNonTerminali = 3;

minNumeroTerminali = 2;
maxNumeroTerminali = 3;

maxProduzioni = 4;

probabilitaEpsilon = 40; (*probabilita' che compaia Epsilon come produzione per un Non Terminale*)

(*Inizializzazione lista per la grammatica finale*)
Clear[grammatica];
grammatica = List[];

(*Per ogni Non Terminale viene generata la sua lista di produzioni*)
Table[
	(*Salviamo il primo Non Terminale in una lista e lo rimuoviamo dalla lista nonTerminali*)
	Clear[listaNonTerminaleEProduzioni];
	listaNonTerminaleEProduzioni = List[];
	AppendTo[listaNonTerminaleEProduzioni, nonTerminali[[1]]];
	nonTerminali = Drop[nonTerminali, 1];
	
	numNonTerminaliRimanenti = numNonTerminali - i;
	
	(*Creazione della stringa di tutte le produzioni per il Non Terminale corrente*)
	If[numNonTerminaliRimanenti > 0, 
		(*Tutti i casi (tranne ultimo)*)
		numElementiNonTerminali = RandomInteger[{1,numNonTerminaliRimanenti}];
		numElementiTerminali = RandomInteger[{minNumeroTerminali,maxNumeroTerminali}];
		
		elementiNonTerminali = nonTerminali[[1;;numElementiNonTerminali]];
		elementiTerminali = terminali[[1;;numElementiTerminali]];
		terminali = Drop[terminali, numElementiTerminali];
		,
		(*Caso ultimo Non Terminale*)	
		numElementiTerminali = RandomInteger[{minNumeroTerminali,maxNumeroTerminali}];
		elementiTerminali = terminali[[1;;numElementiTerminali]];
		elementiNonTerminali = List[];
	];
	elementiDestra = Union[elementiNonTerminali,elementiTerminali];
	elementiDestra = RandomSample[elementiDestra];
	numElementiDestra = Length[elementiDestra];
	
	(*Inizializzazione lista di produzioni per il Non Terminale corrente*)
	Clear[listaProduzioniCorrente];
	listaProduzioniCorrente = List[];
	
	(*Generazione dei punti di suddivisione della stringa per ottenere le produzioni*)
	breaks = Range[2, numElementiDestra];
	numProduzioni = RandomInteger[{1, Min[maxProduzioni, numElementiDestra]}];
	numBreakpoints = numProduzioni - 1;
	breakpoints = Sort[RandomSample[breaks, numBreakpoints]]; (*Indici a cui spezzare la lista di elementi*)
	
	(*Divisione della stringa nelle varie produzioni*)
	If[numBreakpoints == 0,
		(*Caso partizione singola (una sola produzione)*)
		AppendTo[listaProduzioniCorrente, StringRiffle[elementiDestra, ""]];
	,
		(*Caso partizioni/produzioni multiple*)
		Table[
			Which[
			j == 1, (*Prima produzione*)
				indiceUltimoElementoProduzione = breakpoints[[j]] - 1;
				AppendTo[listaProduzioniCorrente, StringRiffle[elementiDestra[[1;;indiceUltimoElementoProduzione]], ""]];
			, 
			j == numProduzioni, (*Ultima produzione*)
				AppendTo[listaProduzioniCorrente, StringRiffle[elementiDestra[[breakpoints[[j - 1]];;-1]], ""]];
			,
			True, (*Produzioni intermedie*)
				indiceUltimoElementoProduzione = breakpoints[[j]] - 1;
				AppendTo[listaProduzioniCorrente, StringRiffle[elementiDestra[[breakpoints[[j - 1]];;indiceUltimoElementoProduzione]], ""]];
			];
		,
		{j, 1, numProduzioni}
		];
	];
	
	(*I Non Terminali successivi al primo possono produrre Epsilon con una determinata percentuale di probabilita'*)	
	If[i > 1,
		If[RandomInteger[99] < probabilitaEpsilon, 
			AppendTo[listaProduzioniCorrente, "\[Epsilon]"];
		]
	]
	
	(*La lista finale con Non Terminale e relative produzioni viene aggiunta alla grammatica*);
	AppendTo[listaNonTerminaleEProduzioni, listaProduzioniCorrente];
	AppendTo[grammatica, listaNonTerminaleEProduzioni];	
			
,
{i,1,numNonTerminali}
];

grammatica


(*GENERAZIONI INSIEMI NULLABLE, FIRST, FOLLOW*)

(* NULLABLE *)
nullable = List[];
Length[grammatica];

(*Per ogni Non Terminale partendo dall'ultimo*)
(*Un Non Terminale potrebbe produrre uno dei Non Terminali successivi, serve sapere se quelli sono annullabili*)
Table[ 
	Clear[currentNull];
	currentNull = {grammatica[[i, 1]], False};
	
	(*Flag da attivare se trovo un elemento annullabile*)
	foundNullable = False;
	
	(*Per ogni produzione finch\[EGrave] non ne trova una annullabile*)
	(*Le iterazioni partono dall'ultima produzione perch\[EGrave] \[Epsilon] \[EGrave] sempre l'ultima*)
	j = Length[grammatica[[i, 2]]];
	While[!foundNullable && j > 0,
		produzioneDaControllare = grammatica[[i, 2, j]] ;
		(*Se trova \[Epsilon] allora il Non Terminale \[EGrave] annullabile*)
		If[produzioneDaControllare == "\[Epsilon]",
			currentNull = {grammatica[[i, 1]], True};
			foundNullable = True;
			,(*Else*)
			isNull = True;
			k = 1;

			(*Controlla tutti i caratteri della produzione corrente*)
			While[isNull && k <= StringLength[produzioneDaControllare],
				(*Se il carattere \[EGrave] un simbolo Terminale allora il Non Terminale non \[EGrave] annullabile*)
				If [MemberQ[CharacterRange["a", "z"], StringTake[produzioneDaControllare, {k}]],
					isNull = False;
					, (*Else*)
					(*Se il carattere \[EGrave] un simbolo Non Terminale devo controllare se \[EGrave] annullabile*)
					Table[
						If[StringTake[produzioneDaControllare, {k}] == nullable[[l, 1]],
							isNull = isNull && nullable[[l, 2]];
						];
					,
					{l, 1, Length[nullable]}
					];
				];
				k++;
			];
			(*Se la produzione \[EGrave] annullabile allora lo \[EGrave] anche il Non Terminale, esce dal ciclo*)
			If[isNull, 
				currentNull = {grammatica[[i, 1]], True};
				foundNullable = True;
			];
		];
	j--;
	];
	PrependTo[nullable, currentNull];
,
{i, Length[grammatica], 1, -1}
];

nullable

(* FIRST *)
(*Inizializzazione della lista di first e liste di supporto temporanee*)
first = List[];
listaNonTerminaleEFirst = List[];
listaFirstCorrente = List[];

(*Ricerca First "ovvi" (sia Terminali che Non Terminali)*)
For[i = 1, i <= numNonTerminali, i++,
\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace] For[j = 1, j <= Length[grammatica[[i,2]]], j++,
		AppendTo[listaFirstCorrente, StringTake[grammatica[[i,2,j]],1]];
\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace] ];

\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace] AppendTo[listaNonTerminaleEFirst, tuttiNonTerminali[[i]]];
\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace] AppendTo[listaNonTerminaleEFirst, listaFirstCorrente];
\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace] AppendTo[first,listaNonTerminaleEFirst];
\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace] 
\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace] Clear[listaFirstCorrente];
\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace] listaFirstCorrente = List[];
\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace] Clear[listaNonTerminaleEFirst];
\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace] listaNonTerminaleEFirst = List[];
];

(*Ricerca First non "ovvi"*)
For[i = numNonTerminali, i >= 1, i--,
	For[j = 1 , j <= Length[grammatica[[i,2]]], j++,
		elementoCorrente = first[[i,2,j]];
		If[ContainsAny[{elementoCorrente},tuttiNonTerminali],
			tuttePosizioni = Position[first,elementoCorrente];
			posizioneFinale = Last[tuttePosizioni];
			posizione = posizioneFinale[[1]];
			terminaliNonOvvi = first[[posizione,2]];
			(*Aggiungiamo i Terminali trovati senza copiarli e rimuoviamo il Non Terminale*)
			first[[i,2]] = Drop[first[[i,2]],{j}];
			first[[i,2]] = Union[first[[i,2]], terminaliNonOvvi];
			(*TODO: caso Non Terminale nullable*)
		]
	]
]

first

(* FOLLOW *)
follow = List[];

(*Itero su tutte le produzioni di tutti i Non Terminali*)
For[i = 2, i <= numNonTerminali, i++,
	nonTerminaleCorrente = tuttiNonTerminali[[i]];
	tuttePosizioni = Position[grammatica,nonTerminaleCorrente];
	(*Rimuovo l'ultima posizione perche' non appartiene a una produzione*)
	tuttePosizioni = Drop[tuttePosizioni,{Length[tuttePosizioni]}];
	
	(*Itero su tutte le posizioni del Non Terminale corrente*)
	For[j = 1, j <= Length[tuttePosizioni], j++, 
		prossimoElemento = 
		
		grammatica[[i,2,j]];
		(*Se trovo un Non Terminale in una Produzione*)
		If[ContainsAny[{prossimoElemento},tuttiNonTerminali],
			
		]
	]
]

follow


(*TABELLA*)
(*grammar = {{"A", " ", " ", "A -> c"}, {"B", "B -> a", "B -> b"}, {"C"," ", "C -> b", "C -> c"}};*)

(*colonne Terminali SOLO dei first*)
colonneTabellaFirst = List[];

Table[ AppendTo[colonneTabellaFirst, first[[i,2]]],
{i, 1, Length[first]}];

colonneTabellaFirst = Union[Flatten[colonneTabellaFirst]];
colonneTabellaFirst = DeleteCases[colonneTabellaFirst, "\[Epsilon]"];
colonneTabellaFirst = AppendTo[colonneTabellaFirst, $]

ListaCelle = List[];

Table[
	tmpCelle = List[];
	Table[
	tmpCelle = Append[tmpCelle, " "],
	{j, 1, Length[colonneTabellaFirst]}
	];
	ListaCelle = Append[ListaCelle, tmpCelle];,
	{i, 1, Length[grammatica[[All,1]]]}
];

ListaCelle

headings = {grammatica[[All,1]],  colonneTabellaFirst};
           
Manipulate[
Text@Grid[Prepend[Flatten /@ Transpose[{headings[[1]], ListaCelle}], 
          PadLeft[headings[[2]], Length@data[[1]] + 1, ""]],
\[NonBreakingSpace]\[NonBreakingSpace] Background -> {None, {Lighter[Yellow, .9], {White,Lighter[Blend[{Blue, Green}], .8]}}},
\[NonBreakingSpace]\[NonBreakingSpace] Dividers -> {{Darker[Gray, .6], {Lighter[Gray, .5]},
	Darker[Gray, .6]}, {Darker[Gray, .6],
	Darker[Gray, .6], {False},
	Darker[Gray, .6]}} Alignment -> {{Left, Right, {Left}}},
	ItemSize -> 6, ItemStyle -> 14,
	Spacings -> {Automatic, .8},
	Editable->False],{i, 1, 20}
	
]


display[a_Association,cursor_Integer: 0,style_Integer: 22,color_: Blue]:=
	Module[{backgrounds},backgrounds=Join[xy[#]->LightGray&/@Select[Range[81],OddQ[block[#]]&],
	xy[#]->LightRed&/@simpleConflicts[a]];
	
	Grid[colonneTabellaFirst,righeTabella,
	Frame->If[MatchQ[a[cursor],_Integer],All,{All,All,{xy[cursor]->{Thick,Blue}}}],
	Background->{White,White,backgrounds},ItemStyle->{Automatic,Automatic,xy[#]->color&/@First/@blues[a]},
	ItemSize->{style/22.0,style/18.0},BaseStyle->{style,Bold}]]

displaySln[a_Association]:=display[a,0,13,Black]


loc[{x_,y_}]:=1+Floor[9 x]+9 Floor[9 (1-y)]

Manipulate[
Grid[{
{Which[
validSln[puzzle],Style["Correct solution!",Bold,Blue],
finished[puzzle],Style["You have errors.",Bold,Red],
True, Style["Click on blank square:","Label"]]
},
{
Column[{
EventHandler[Dynamic[display[puzzle,cursor]],"MouseClicked":>(cursor=loc[MousePosition["EventHandlerScaled"]])],
Column[{Style["Select value:","Label"],EventHandler[Grid[{{" ",1,2,3,4,5,6,7,8,9}},Frame->All,BaseStyle->Large],"MouseClicked":>Module[{digt =Floor[10First@ MousePosition["EventHandlerScaled"]]},
If[digt == 0,KeyDropFrom[puzzle,cursor],puzzle[cursor]={digt}]]]
}]
}],
" ",
If[showSolution,displaySln[solution],""]
}
}],
{solution,ControlType->None},
{{puzzle, (solution=randFill[];createPuzzle[solution])},ControlType->None},
{{cursor,0},ControlType->None},
Button["New Game",(
cursor=0 ; 
showSolution=False;
solution=randFill[];
puzzle=createPuzzle[solution];
)&],
{{showSolution,False,"show solution"},{True,False}},
SaveDefinitions->True,
ContentSize->{620, 420}
]

(*Manipulate[
TextGrid[Prepend[grammar, colonneTabellaFirst],
Background -> {None, {Lighter[Yellow, .9]}},
\[NonBreakingSpace]\[NonBreakingSpace] Dividers -> {{Darker[Gray, .6], {Lighter[Gray, .5]},
	Darker[Gray, .6]}, {Darker[Gray, .6],
	Darker[Gray, .6], {False},
	Darker[Gray, .6]}} Alignment -> {{Left, Right, {Left}}},
	ItemSize -> {{3, 6, 6, 6}}, ItemStyle -> 14,
	Spacings -> {Automatic, .8}],{i, 0,9}
]*)


End[]


EndPackage[]
