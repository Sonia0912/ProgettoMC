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

SeedRandom[2];

(*Parametri*)
tuttiNonTerminali = CharacterRange["A", "D"];
tuttiTerminali = CharacterRange["a", "l"];

nonTerminali = tuttiNonTerminali;
nonTerminali = Drop[nonTerminali, 1];
nonTerminaliIndici = tuttiNonTerminali;
terminali = tuttiTerminali;

numNonTerminali = Length[tuttiNonTerminali];
numTerminali = Length[terminali];

maxNumeroNonTerminali = 2;

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
  	AppendTo[listaNonTerminaleEProduzioni, nonTerminaliIndici[[1]]];
  	nonTerminaliIndici = Drop[nonTerminaliIndici, 1];
  	
  	numNonTerminaliRimanenti = Length[nonTerminali];
  	
  	(*
  	(*Creazione della stringa di tutte le produzioni per il Non Terminale corrente*)
  	If[numNonTerminaliRimanenti > 0, 
  		(*Tutti i casi (tranne ultimo)*)
  		numElementiNonTerminali = RandomInteger[{1, numNonTerminaliRimanenti}];
  		numElementiTerminali = RandomInteger[{minNumeroTerminali, maxNumeroTerminali}];
  		
  		elementiNonTerminali = nonTerminali[[1;;numElementiNonTerminali]];
  		elementiTerminali = terminali[[1;;numElementiTerminali]];
  		terminali = Drop[terminali, numElementiTerminali];
  		,
  		(*Caso ultimo Non Terminale*)	
  		numElementiTerminali = RandomInteger[{minNumeroTerminali, maxNumeroTerminali}];
  		elementiTerminali = terminali[[1;;numElementiTerminali]];
  		elementiNonTerminali = List[];
  	];
  	*)
  	
  	(*Creazione della stringa di tutte le produzioni per il Non Terminale corrente*)
  	If[numNonTerminaliRimanenti > 0, 
   		(*Ci sono ancora Non Terminali inutilizzati*)
   		numElementiNonTerminali = RandomInteger[{1, Min[maxNumeroNonTerminali, numNonTerminaliRimanenti]}];
   		elementiNonTerminali = nonTerminali[[1 ;; numElementiNonTerminali]];
   		nonTerminali = Drop[nonTerminali, numElementiNonTerminali];
   		numElementiTerminali = RandomInteger[{minNumeroTerminali, maxNumeroTerminali}];
   		elementiTerminali = terminali[[1 ;; numElementiTerminali]];
   		terminali = Drop[terminali, numElementiTerminali];
   		,
   		(*Sono stati usati tutti i Non terminali*)	
   		numElementiTerminali = RandomInteger[{minNumeroTerminali, maxNumeroTerminali}];
   		elementiTerminali = terminali[[1 ;; numElementiTerminali]];
   	    terminali = Drop[terminali, numElementiTerminali];
   		elementiNonTerminali = List[];
   	];
  	elementiDestra = Union[elementiNonTerminali, elementiTerminali];
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
       				AppendTo[listaProduzioniCorrente, StringRiffle[elementiDestra[[1 ;; indiceUltimoElementoProduzione]], ""]];
       			, 
       			j == numProduzioni, (*Ultima produzione*)
       				AppendTo[listaProduzioniCorrente, StringRiffle[elementiDestra[[breakpoints[[j - 1]] ;; -1]], ""]];
       			,
       			True, (*Produzioni intermedie*)
       				indiceUltimoElementoProduzione = breakpoints[[j]] - 1;
       				AppendTo[listaProduzioniCorrente, StringRiffle[elementiDestra[[breakpoints[[j - 1]] ;; indiceUltimoElementoProduzione]], ""]];
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
  {i, 1, numNonTerminali}
  ];

grammatica


(*FUNZIONI AUSILIARIE*)

(*Ritorna i First di un Non Terminale*)
getFirst[NT_] := (
	posizione = Position[first,NT];
	posizioneFlat = Flatten[posizione];
	firstNT = first[[posizioneFlat[[1]],2]];
	firstNT	
)

(*Ritorna True se il Non Terminale e' nullable, False se non e' nullable*)
checkNullabilita[NT_] := (
	posNTinNullable = Position[nullable, NT];
	indiceNTinNullable = posNTinNullable[[1, 1]];
	nullabilita = nullable[[indiceNTinNullable,2]];
	nullabilita
)

(*Data una produzione, le colonne e la riga in cui inserirla, la inserisce nella soluzione*)
inserisciProduzione[prod_, colonne_, riga_] := (
	Table[
		Table[
			If[soluzione[[1,c]]==colonne[[r]],
				soluzione[[riga]] = ReplacePart[soluzione[[riga]], c -> prod];
			];
			,
			{r, 1, Length[colonne],1}
		];
		,
		{c, 1, numColonne, 1}
	];
)

(*Ritorna una lista di Terminali rimouvendo, se ci sono, Non Terminali e \[Epsilon]*)
rimuoviNTeEps[lista_] := (
	nuovaLista = lista;
	Table[
		If[ContainsAny[{nuovaLista[[k]]},tuttiNonTerminali] || ContainsAny[{nuovaLista[[k]]},{"\[Epsilon]"}],
			nuovaLista = Drop[nuovaLista, {k}];
		];
		,
		{k, 1, Length[nuovaLista], 1}
	];
	nuovaLista
)


(* NULLABLE *)

nullable = List[];
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
					isNull = isNull && nullable[[Flatten[Position[nullable, StringTake[produzioneDaControllare, {k}]]][[1]], 2]];
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
Table[
\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace] Table[
		AppendTo[listaFirstCorrente, StringTake[grammatica[[i,2,j]],1]];
		,
		{j, 1, Length[grammatica[[i,2]]], 1}
\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace] ];

\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace] AppendTo[listaNonTerminaleEFirst, tuttiNonTerminali[[i]]];
\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace] AppendTo[listaNonTerminaleEFirst, listaFirstCorrente];
\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace] AppendTo[first,listaNonTerminaleEFirst];
\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace] 
\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace] Clear[listaFirstCorrente];
\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace] listaFirstCorrente = List[];
\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace] Clear[listaNonTerminaleEFirst];
\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace] listaNonTerminaleEFirst = List[];
\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace] ,
\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace] {i, 1, numNonTerminali, 1}
];

(*Mettiamo Epsilon ai Non Terminali nullable*)
Table[
	If[nullable[[i,2]],
		first[[i,2]] = Union[first[[i,2]], {"\[Epsilon]"}];
	];
	,
	{i, 1, numNonTerminali, 1}
];

(*Ricerca First "non ovvi"*)
Table[
	Table[
		elementoCorrente = first[[i,2,j]];
		If[ContainsAny[{elementoCorrente},tuttiNonTerminali],
			(*Cerchiamo i first di quel Non Terminale che saranno i first "non ovvi" del Terminale che stiamo valutando*)
			tuttePosizioni = Position[first,elementoCorrente];
			posizioneFinale = Last[tuttePosizioni];
			posizione = posizioneFinale[[1]];
			terminaliNonOvvi = first[[posizione,2]];
			(*Rimuoviamo il Non Terminale dalla lista di first*)
			first[[i,2]] = Drop[first[[i,2]],{j}];
			
			(*Se c'e', rimuoviamo \[Epsilon] tra i Terminali da aggiungere*)
			If[ContainsAny[{"\[Epsilon]"},terminaliNonOvvi],
				posizione = Position[terminaliNonOvvi, "\[Epsilon]"];
				terminaliNonOvvi = Drop[terminaliNonOvvi, Flatten[posizione]];
			];
			(*Aggiungiamo i Terminali senza duplicati*)
			first[[i,2]] = Union[first[[i,2]], terminaliNonOvvi];
			
			(*Controlliamo se il Non Terminale e' nullable*)
			nullabilita = checkNullabilita[elementoCorrente];
			
			(*Prendiamo la produzione in cui compare quel NT*)
			produzione = "";
			Table[
				If[StringTake[grammatica[[i,2,prod]],{1}] == elementoCorrente,
					produzione = grammatica[[i,2,prod]];
				];
				,
				{prod, 1, Length[grammatica[[i,2]]], 1}
			];
					
			successivo = 2; (*Step a cui siamo nella produzione*)			
			
			While[nullabilita,
				If[StringLength[produzione] >= successivo,
					elementoSuccessivo = StringTake[produzione,{successivo}];
					Which[
						(*Il successivo e' un Non Terminale -> aggiungiamo i suoi First ai First del Non Terminale corrente*)
						ContainsAny[{elementoSuccessivo},tuttiNonTerminali],
							(*Aggiungiamo i First*)
							posNTinFirst = Last[Position[first, elementoSuccessivo]][[1]];
							terminaliDaAggiungere = first[[posNTinFirst, 2]];
							
							(*Se ci sono rimuoviamo i Non Terminali e \[Epsilon]*)
							terminaliDaAggiungere = rimuoviNTeEps[terminaliDaAggiungere];
							first[[i,2]] = Union[first[[i,2]], terminaliDaAggiungere];
							
							(*Controlliamo se anche questo e' nullable*)
							nullabilita = checkNullabilita[elementoSuccessivo];
							(*Aumentiamo successivo per vedere cosa c'\[EGrave] dopo*)
							successivo = successivo+1;
						, 
						(*Il successivo e' un Terminale -> aggiungiamo il Terminali ai First*)
						ContainsAny[{elementoSuccessivo},tuttiTerminali], 
							first[[i,2]] = Union[first[[i,2]], {elementoSuccessivo}];
							nullabilita = False;
						,
						(*E' vuoto -> non aggiungiamo niente *)
						True,
							nullabilita = False;
					];
					,
					nullabilita = False;
				];
			];
			(*Decrementiamo j perche' avendo tolto il NT dalla lista di first gli indici sono cambiati*)
			j--;			
		];
		,
		{j, 1, Length[first[[i,2]]], 1}
	];
	,
	{i, numNonTerminali, 1, -1}
];

first


(* FOLLOW *)

follow = {{"A", {"$"}}};
listaRicontrollo1 = List[];
listaRicontrollo2 = List[];

(*Inizializzazione lista di Follow*)
Table[
	AppendTo[follow, {tuttiNonTerminali[[i]], {}}]
,{i, 2, numNonTerminali}
];

(*Itero su tutte le produzioni di tutti i Non Terminali*)
Table[ (*Per ogni Non Terminale*)
	Table[(*Per ogni produzione del Non Terminale*)
		produzioneCorrente = grammatica[[i, 2, j]];
		Table[(*Per ogni carattere della produzione*)
			If[MemberQ[tuttiNonTerminali, StringTake[produzioneCorrente, {k}]],
			(*Se il carattere \[EGrave] un Non Terminale ci sono 3 casi*)
				nonTerminaleDaControllare = StringTake[produzioneCorrente, {k}];
				Which[
					(*Se \[EGrave] l'ultimo elemento della produzione*)
					k == StringLength[produzioneCorrente],
						(*Bisogner\[AGrave] aggiungere al Follow del Non Terminale corrente il Follow del Non Terminale che lo produce*)
						AppendTo[listaRicontrollo1, {nonTerminaleDaControllare, grammatica[[i, 1]]}];
					,
					(*Se il prossimo elemento \[EGrave] un Terminale lo aggiungo al Follow del Non Terminale corrente*)
					MemberQ[tuttiTerminali, StringTake[produzioneCorrente, {k + 1}]],
						AppendTo[follow[[Flatten[Position[follow, nonTerminaleDaControllare]][[1]], 2]], StringTake[produzioneCorrente, {k + 1}]];
					,
					(*Se il prossimo elemento \[EGrave] un Non Terminale aggiungo il suo First (senza \[Epsilon]) al Follow del Non Terminale corrente*)
					MemberQ[tuttiNonTerminali, StringTake[produzioneCorrente, {k + 1}]],
						firstProssimoNonTerminale =  first[[Flatten[Position[first, StringTake[produzioneCorrente, {k + 1}]]][[1]], 2]];
						If[MemberQ[firstProssimoNonTerminale, "\[Epsilon]"],
							firstProssimoNonTerminale = Drop[firstProssimoNonTerminale, Flatten[Position[firstProssimoNonTerminale, "\[Epsilon]"]]];
						];
						AppendTo[follow[[Flatten[Position[follow, nonTerminaleDaControllare]][[1]], 2]], firstProssimoNonTerminale];
						
						(*Se il Non Terminale successivo \[EGrave] Nullable bisogner\[AGrave] aggiungere il suo Follow a quello del Non Terminale corrente*)
						If[nullable[[Flatten[Position[nullable, StringTake[produzioneCorrente, {k + 1}]]][[1]], 2]],
							PrependTo[listaRicontrollo2, {nonTerminaleDaControllare, StringTake[produzioneCorrente, {k + 1}]}];
						];
				];
			];
		,{k, 1, StringLength[produzioneCorrente]}
		];
	,{j, 1, Length[grammatica[[i, 2]]]}
	];
,{i, 1, numNonTerminali}
];

(*Ad ogni Non Terminale in ultima posizione in una produzione viene aggiunto il Follow del Non Terminale che lo ha prodotto*)
Table[	
	AppendTo[follow[[Flatten[Position[follow, listaRicontrollo1[[i, 1]]]][[1]], 2]], follow[[Flatten[Position[follow, listaRicontrollo1[[i, 2]]]][[1]], 2]]];
,{i, 1, Length[listaRicontrollo1]}
];

(*Ad ogni Non Terminale che precede un Non Terminale Nullable viene aggiunto il Follow del Non Terminale Nullable*)
Table[
	AppendTo[follow[[Flatten[Position[follow, listaRicontrollo2[[i, 1]]]][[1]], 2]], follow[[Flatten[Position[follow, listaRicontrollo2[[i, 2]]]][[1]], 2]]];
,{i, 1, Length[listaRicontrollo2]}
];

Table[
	follow[[i, 2]] = Flatten[follow[[i, 2]]];
	DeleteDuplicates[follow[[i, 2]]];
	Sort[follow[[i, 2]]];
,{i, 1, Length[follow]}	
];

follow


(*GENERAZIONE DELLA SOLUZIONE*)

soluzione = List[];

colonne = tuttiTerminali;
colonne = Prepend[colonne, " "];
AppendTo[colonne, "$"];
numColonne = Length[colonne];
AppendTo[soluzione, colonne];

rigaCorrente = List[];

For[i = 1, i <= numNonTerminali, i++,

	(*Inizializziamo la riga di quel Non Terminale*)
	For[h = 1, h <= numColonne, h++,
		AppendTo[rigaCorrente, " "];
	];
	(*Il primo elemento della riga sara' il NT corrente*)
	rigaCorrente = ReplacePart[rigaCorrente, 1 -> tuttiNonTerminali[[i]]];
	AppendTo[soluzione, rigaCorrente];
	
	(*Cicliamo su tutte le produzioni del NT corrente*)
	For[j = 1, j <= Length[grammatica[[i,2]]], j++,
		produzione = grammatica[[i,2,j]];
		primoElemento = StringTake[produzione,1];
		produzioneIntera = StringJoin[tuttiNonTerminali[[i]], "->", produzione];
		(*Controlliamo se la produzione inizia con un Terminale o con un Non Terminale*)
		Which[
			(*Caso Terminale*)
			ContainsAny[{primoElemento}, tuttiTerminali],
				(*Mettiamo la produzione nella colonna di quel Terminale*)
				posizione = Position[soluzione[[1]],primoElemento];
				posizioneFlat = Flatten[posizione];
				soluzione[[i+1]] = ReplacePart[soluzione[[i+1]], posizioneFlat[[1]] -> produzioneIntera];
			,
			(*Caso Non Terminale*)
			ContainsAny[{primoElemento}, tuttiNonTerminali],
				(*Prendiamo i fisrt di quel NT, saranno le colonne in cui mettere la produzione*)
				firstNT = getFirst[primoElemento];
				(*Prendiamo le posizioni di quei Terminali nelle colonne e rimpiazziamo*)
				inserisciProduzione[produzioneIntera, firstNT, i+1];
				
				(*Caso in cui il NT e' nullable*)
				nullabilita = checkNullabilita[primoElemento];
				successivo = 2;
				While[nullabilita,
					If[StringLength[produzione] >= successivo,
						elementoSuccessivo = StringTake[produzione,{successivo}];
						
						Which[
							(*Il successivo e' un Non Terminale -> mettiamo la produzione nelle colonne dei First di quel NT*)
							ContainsAny[{elementoSuccessivo},tuttiNonTerminali],					
								(*Prendiamo i fisrt di quel NT, saranno le colonne in cui mettere la produzione*)
								firstNT = getFirst[elementoSuccessivo];
								(*Prendiamo le posizioni di quei Terminali nelle colonne e rimpiazziamo*)
								inserisciProduzione[produzioneIntera, firstNT, i+1];

								(*Controlliamo se anche questo e' nullable*)
								nullabilita = checkNullabilita[elementoSuccessivo];
								(*Aumentiamo successivo per vedere cosa c'\[EGrave] dopo*)
								successivo = successivo+1;
							, 
							(*Il successivo e' un Terminale -> mettiamo la produzione nella colonna di quel Terminale*)
							ContainsAny[{elementoSuccessivo},tuttiTerminali],
								posizione = Position[soluzione[[1]],elementoSuccessivo];
								posizioneFlat = Flatten[posizione];
								soluzione[[i+1]] = ReplacePart[soluzione[[i+1]], posizioneFlat[[1]] -> produzioneIntera];
								nullabilita = False;
							,
							(*E' vuoto -> non aggiungiamo niente *)
							True,
								nullabilita = False;
						];					
						,
						nullabilita = False;
					];
				
				];
			,
			(*Caso Epsilon*)
			True,
				followNT = follow[[i,2]];
				(*Prendiamo le posizioni di quei Terminali nelle colonne e rimpiazziamo*)
				inserisciProduzione[produzioneIntera, followNT, i+1];
		];
	];
	
	(*Reinizializziamo rigaCorrente*)
	Clear[rigaCorrente];
    rigaCorrente = List[];
];

Print["Grammatica: ", grammatica];
Print["First: ", first];
Print["Follow: ", follow];
soluzione // MatrixForm

<<<<<<< Updated upstream

(*TABELLA*)
(*colonne Terminali SOLO dei first*)
colonneTabellaFirst = List[];
=======
listaProduzioni = List[];
Table[
	Table[
		AppendTo[listaProduzioni, StringJoin[grammatica[[i, 1]], " \[RightArrow] ", grammatica[[i, 2, j]]]];
	,{j, 1, Length[grammatica[[i, 2]]]}
	];
,{i, 1, Length[grammatica]}
];
listaProduzioni		


(*grammar = {{" ", "a", "b", "d", "f", "g", "l", "m", "$"},
			{"A", "A->aB", "A->bC", " ", " ", " ", " ", " ", " "}, 
			{"B", " ", " ", "B->d", "B->Ce", "B->Ce", " ", " ", " "}, 
			{"C", " ", " ", " ", "C->fD", "C->gh ", " ", " ", " "},
			{"D", " ", " ", " ", " ", " ", "D->l", "D->m", " "}};*)
grammar = soluzione;
>>>>>>> Stashed changes

rows = Length[grammar[[All,1]]](*numero dei terminali*)
cols = Length[grammar[[1,All]]] (*numero dei non terminali*)

(*calcola l'esatta riga e colonna di ogni cella della tabella*)
row[n_]:=Quotient[n-1,cols]+1;
col[n_]:=Mod[n-1,cols]+1;
(*data la cella n restituisce riga e colonna corrispondenti*)
xy[n_]:={row[n],col[n]}


displayFirstFollow[g_]:=Grid[g,
			 Frame -> All, 
			 Background->{White,White},
			 ItemStyle->{Automatic},
			 ItemSize->{{2,{2}}},
		     BaseStyle->{Bold}
			 Editable -> False]
			 
displayFirstFollowSln[g_]:=displayFirstFollow[g]

display[g_,cursor_:0]:=
	(*Module[{backgrounds},
		backgrounds = {If[checkErrors[g, cursor], xy[cursor]->LightRed]}; *)
		Grid[g,
		Frame->If[MatchQ[xy[cursor],_Integer],All,{All,All,{xy[cursor]->{Thick,Blue}}}],
		Background->{White,White},
		ItemStyle->{Automatic},
		ItemSize->{{3,{5}}},
		BaseStyle->{Bold}]

displaySln[g_]:=display[g,0]

checkErrors[g_, cursor_]:= If[g[[xy[cursor][[1]], xy[cursor][[2]]]] != grammar[[xy[cursor][[1]], xy[cursor][[2]]]], True, False]	
			

createEmptyGrammar[sln_] := 
	Module[{copy = sln}, Table[ If[i > 1 && j > 1, copy[[i, j]] = " "], {i, rows}, {j, cols} ]; copy ]

createEmptyCheckbox[sln_]:= 
	Module[{copy = sln}, Table[ If[i > 1 && j > 1, copy[[i, j]] = Checkbox[]], {i, rows}, {j, cols} ]; copy ]

(*Mappiamo il click del mouse sulla tabella a un numero che identifica in maniera univoca la cella cliccata*)
loc[{x_, y_}] := 1 + Floor[cols x] + cols Floor[(1 - y) rows]
tmp = soluzione[[All,1]]
tmp = Delete[soluzione[[All,1]], 1]



<<<<<<< Updated upstream
headings = {grammatica[[All,1]],  colonneTabellaFirst};
           
(*Manipulate[
Text@Grid[Prepend[Flatten /@ Transpose[{headings[[1]], ListaCelle}], 
          PadLeft[headings[[2]], Length@headings[[1]] + 1, ""]],
\[NonBreakingSpace]\[NonBreakingSpace] Background -> {None, {Lighter[Yellow, .9], {White,Lighter[Blend[{Blue, Green}], .8]}}},
\[NonBreakingSpace]\[NonBreakingSpace] Dividers -> {{Darker[Gray, .6], {Lighter[Gray, .5]},
	Darker[Gray, .6]}, {Darker[Gray, .6],
	Darker[Gray, .6], {False},
	Darker[Gray, .6]}} Alignment -> {{Left, Right, {Left}}},
	ItemSize -> 6, ItemStyle -> 14,
	Spacings -> {Automatic, .8},
	Editable->False],{i, 1, 20}
	
]*)


grammar = {{" ", "a", "b", "d", "f", "g", "l", "m", "$"},
			{"A", "A->aB", "A->bC", " ", " ", " ", " ", " ", " "}, 
			{"B", " ", " ", "B->d", "B->Ce", "B->Ce", " ", " ", " "}, 
			{"C", " ", " ", " ", "C->fD", "C->gh ", " ", " ", " "},
			{"D", " ", " ", " ", " ", " ", "D->l", "D->m", " "}};
produzioni = 10;			
rows = Length[grammar[[All,1]]];
cols = Length[grammar[[1,All]]];

(*calcola l'esatta riga e colonna di ogni cella della tabella*)
row[n_]:=Quotient[n-1,cols]+1;
col[n_]:=Mod[n-1,cols]+1;
(*data la cella n restituisce riga e colonna corrispondenti*)
xy[n_]:={row[n],col[n]}

listaProduzioni = {"A->aB", "A->bC", "B->d", "B->Ce", "C->fD", "C->gh", "D->l", "D->m"};


display[g_,cursor_:0]:=
	Grid[g,
		Frame->If[MatchQ[xy[cursor],_Integer],All,{All,All,{xy[cursor]->{Thick,Blue}}}],
		Background->{White,White,backgrounds},
		ItemStyle->{Automatic},
		ItemSize->{{3,{5}}},
		BaseStyle->{Bold}]

displaySln[g_]:=display[g,0]

checkErrors[g_, cursor_]:=
	If[g[[xy[cursor][[1]], xy[cursor][[2]]]]==grammar[[xy[cursor][[1]], xy[cursor][[2]]]],
			Join[xy[cursor]->{LightRed}]]

(*questa sar\[AGrave] la func contenente tutto l'algo per generare la grammatica*)
createSol[g_]:=grammar;

createEmptyGrammar[sln_] := 
	Module[{copy = sln}, Table[ If[i > 1 && j > 1, copy[[i, j]] = " "], {i, rows}, {j, cols} ]; copy ]

(*Mappiamo il click del mouse sulla tabella a un numero che identifica in maniera univoca la cella cliccata*)
loc[{x_, y_}] := 1 + Floor[cols x] + cols Floor[(1 - y) rows]


Manipulate[
	Grid[{
	{Which[
		(*inserire if tabella completata stampa sol corretta o hai errori*)
		True, Style["Click on blank square:","Label"]]
	},
	{
	Column[{
		EventHandler[
			Dynamic[display[emptyGrammar,cursor]],
			"MouseClicked":>(
			If[MemberQ[Range[1, rows*cols, 9],loc[MousePosition["EventHandlerScaled"]]] || 
				MemberQ[Range[2, cols],loc[MousePosition["EventHandlerScaled"]]],
				cursor = -1,
				cursor = loc[MousePosition["EventHandlerScaled"]]
				]
			)], 
	Row[  
		Table[With[{i = i},\[NonBreakingSpace]
\[NonBreakingSpace]       Button[listaProduzioni[[i]],
\[NonBreakingSpace]              emptyGrammar[[xy[cursor][[1]], xy[cursor][[2]]]]=listaProduzioni[[i]]; 
\[NonBreakingSpace]       ]], 
\[NonBreakingSpace]       {i, 1, Length[listaProduzioni]}],Spacer[0.5]     
\[NonBreakingSpace]           
    ],
    Row[{
        Button["Clear", emptyGrammar[[xy[cursor][[1]], xy[cursor][[2]]]]= " "],
        Button["Clear All", Table[emptyGrammar[[i,j]] = " ", {i, 2, rows}, {j, 2, cols}]]
        }],
    (*rimuovi puntatore da tabella soluzione *)
    If[showSolution,Row[{displaySln[solution]}],""]
    },
    Alignment -> Center
    ],
	" "	
	}
	}],
	{solution,ControlType->None},
	{{emptyGrammar, (solution=grammar;createEmptyGrammar[solution])},ControlType->None},
{{cursor,0},ControlType->None},
Button["Nuovo esercizio",(
cursor=0 ; 
showSolution=False;
solution=grammar;
emptyGrammar=createEmptyGrammar[solution];
)&],
{{showSolution,False,"show solution"},{True,False}},
SaveDefinitions->True,
ContentSize->{650, 420}
]






(* ::Input:: *)
(*Manipulate[Grid[{{Which[True, Style["Click on blank square:", "Label"]]}, *)
(*    {Column[{EventHandler[Dynamic[AnalisiSintattica`Private`display[*)
(*          AnalisiSintattica`Private`emptyGrammar, *)
(*          AnalisiSintattica`Private`cursor]], "MouseClicked" :> *)
(*         If[MemberQ[Range[1, AnalisiSintattica`Private`rows**)
(*              AnalisiSintattica`Private`cols, 9], *)
(*            AnalisiSintattica`Private`loc[MousePosition[*)
(*              "EventHandlerScaled"]]] || MemberQ[Range[2, *)
(*             AnalisiSintattica`Private`cols], AnalisiSintattica`Private`loc[*)
(*             MousePosition["EventHandlerScaled"]]], *)
(*          AnalisiSintattica`Private`cursor = -1, *)
(*          AnalisiSintattica`Private`cursor = AnalisiSintattica`Private`loc[*)
(*            MousePosition["EventHandlerScaled"]]]], *)
(*       Row[Table[With[{AnalisiSintattica`Private`i$ = *)
(*            AnalisiSintattica`Private`i}, Button[*)
(*           AnalisiSintattica`Private`listaProduzioni[[*)
(*            AnalisiSintattica`Private`i$]], *)
(*           AnalisiSintattica`Private`emptyGrammar[[*)
(*             AnalisiSintattica`Private`xy[AnalisiSintattica`Private`cursor][[*)
(*              1]],AnalisiSintattica`Private`xy[*)
(*               AnalisiSintattica`Private`cursor][[2]]]] = *)
(*            AnalisiSintattica`Private`listaProduzioni[[*)
(*             AnalisiSintattica`Private`i$]]]], {AnalisiSintattica`Private`i, *)
(*          1, Length[AnalisiSintattica`Private`listaProduzioni]}], *)
(*        Spacer[0.5]], Row[{Button["Clear", *)
(*          AnalisiSintattica`Private`emptyGrammar[[*)
(*            AnalisiSintattica`Private`xy[AnalisiSintattica`Private`cursor][[*)
(*             1]],AnalisiSintattica`Private`xy[*)
(*              AnalisiSintattica`Private`cursor][[2]]]] = " "], *)
(*         Button["Clear All", Table[AnalisiSintattica`Private`emptyGrammar[[*)
(*             AnalisiSintattica`Private`i,AnalisiSintattica`Private`j]] = " ", *)
(*           {AnalisiSintattica`Private`i, 2, AnalisiSintattica`Private`rows}, *)
(*           {AnalisiSintattica`Private`j, 2, *)
(*            AnalisiSintattica`Private`cols}]]}], *)
(*       If[AnalisiSintattica`Private`showSolution, *)
(*        Row[{AnalisiSintattica`Private`displaySln[*)
(*           AnalisiSintattica`Private`solution], Enabled -> False}], ""]}, *)
(*      Alignment -> Center], " "}}], {{AnalisiSintattica`Private`solution, *)
(*    {{" ", "a", "b", "d", "f", "g", "l", "m", "$"}, *)
(*     {"A", "A->aB", "A->bC", " ", " ", " ", " ", " ", " "}, *)
(*     {"B", " ", " ", "B->d", "B->Ce", "B->Ce", " ", " ", " "}, *)
(*     {"C", " ", " ", " ", "C->fD", "C->gh ", " ", " ", " "}, *)
(*     {"D", " ", " ", " ", " ", " ", "D->l", "D->m", " "}}}, *)
(*   ControlType -> None}, {{AnalisiSintattica`Private`emptyGrammar, *)
(*    {{" ", "a", "b", "d", "f", "g", "l", "m", "$"}, *)
(*     {"A", " ", " ", " ", " ", " ", " ", " ", " "}, *)
(*     {"B", " ", " ", " ", " ", " ", " ", " ", " "}, *)
(*     {"C", " ", " ", " ", " ", " ", " ", " ", " "}, *)
(*     {"D", " ", " ", " ", " ", " ", " ", " ", " "}}}, ControlType -> None}, *)
(*  {{AnalisiSintattica`Private`cursor, 0}, ControlType -> None}, *)
(*  Button["New Game", (AnalisiSintattica`Private`cursor = 0; *)
(*     AnalisiSintattica`Private`showSolution = False; *)
(*     AnalisiSintattica`Private`solution = AnalisiSintattica`Private`grammar; *)
(*     AnalisiSintattica`Private`emptyGrammar = *)
(*      AnalisiSintattica`Private`createEmptyGrammar[*)
(*       AnalisiSintattica`Private`solution]; ) & ], *)
(*  {{AnalisiSintattica`Private`showSolution, True, "show solution"}, *)
(*   {True, False}}, ContentSize -> {650, 420}, *)
(*  Initialization :> {AnalisiSintattica`Private`display[*)
(*      AnalisiSintattica`Private`g_AnalisiSintattica`Private`solution, *)
(*      AnalisiSintattica`Private`cursor_Integer:0] := *)
(*     Grid[AnalisiSintattica`Private`g, *)
(*      Frame -> If[MatchQ[AnalisiSintattica`Private`xy[*)
(*          AnalisiSintattica`Private`cursor], _Integer], All, *)
(*        {All, All, {AnalisiSintattica`Private`xy[*)
(*            AnalisiSintattica`Private`cursor] -> {Thick, Blue}}}], *)
(*      Background -> {White, White, White}, ItemStyle -> {Automatic}, *)
(*      ItemSize -> {{Automatic, {Automatic}}}, BaseStyle -> {Bold}], *)
(*    AnalisiSintattica`Private`display[AnalisiSintattica`Private`g_Null, *)
(*      AnalisiSintattica`Private`cursor_Integer:0] := *)
(*     Grid[AnalisiSintattica`Private`g, *)
(*      Frame -> If[MatchQ[AnalisiSintattica`Private`xy[*)
(*          AnalisiSintattica`Private`cursor], _Integer], All, *)
(*        {All, All, {AnalisiSintattica`Private`xy[*)
(*            AnalisiSintattica`Private`cursor] -> {Thick, Blue}}}], *)
(*      Background -> {White, White, White}, ItemStyle -> {Automatic}, *)
(*      ItemSize -> {{Automatic, {Automatic}}}, BaseStyle -> {Bold}], *)
(*    AnalisiSintattica`Private`display[AnalisiSintattica`Private`g:*)
(*       Blank[AnalisiSintattica`Private`createSol[*)
(*         {{" ", "a", "b", "d", "f", "g", "l", "m", "$"}, *)
(*          {"A", "A->aB", "A->bC", " ", " ", " ", " ", " ", " "}, *)
(*          {"B", " ", " ", "B->d", "B->Ce", "B->Ce", " ", " ", " "}, *)
(*          {"C", " ", " ", " ", "C->fD", "C->gh ", " ", " ", " "}, *)
(*          {"D", " ", " ", " ", " ", " ", "D->l", "D->m", " "}}]], *)
(*      AnalisiSintattica`Private`cursor_Integer:0] := *)
(*     Grid[AnalisiSintattica`Private`g, *)
(*      Frame -> If[MatchQ[AnalisiSintattica`Private`xy[*)
(*          AnalisiSintattica`Private`cursor], _Integer], All, *)
(*        {All, All, {AnalisiSintattica`Private`xy[*)
(*            AnalisiSintattica`Private`cursor] -> {Thick, Blue}}}], *)
(*      Background -> {White, White, White}, ItemStyle -> {Automatic}, *)
(*      ItemSize -> {{Automatic, {Automatic}}}, BaseStyle -> {Bold}], *)
(*    AnalisiSintattica`Private`display[AnalisiSintattica`Private`g:*)
(*       Blank[{{" ", "a", "b", "d", "f", "g", "l", "m", "$"}, *)
(*         {"A", "A->aB", "A->bC", " ", " ", " ", " ", " ", " "}, *)
(*         {"B", " ", " ", "B->d", "B->Ce", "B->Ce", " ", " ", " "}, *)
(*         {"C", " ", " ", " ", "C->fD", "C->gh ", " ", " ", " "}, *)
(*         {"D", " ", " ", " ", " ", " ", "D->l", "D->m", " "}}], *)
(*      AnalisiSintattica`Private`cursor_Integer:0] := *)
(*     Grid[AnalisiSintattica`Private`g, *)
(*      Frame -> If[MatchQ[AnalisiSintattica`Private`xy[*)
(*          AnalisiSintattica`Private`cursor], _Integer], All, *)
(*        {All, All, {AnalisiSintattica`Private`xy[*)
(*            AnalisiSintattica`Private`cursor] -> {Thick, Blue}}}], *)
(*      Background -> {White, White, White}, ItemStyle -> {Automatic}, *)
(*      ItemSize -> {Automatic}, BaseStyle -> {Bold}], *)
(*    AnalisiSintattica`Private`display[AnalisiSintattica`Private`g_, *)
(*      AnalisiSintattica`Private`cursor_:0] := *)
(*     Grid[AnalisiSintattica`Private`g, *)
(*      Frame -> If[MatchQ[AnalisiSintattica`Private`xy[*)
(*          AnalisiSintattica`Private`cursor], _Integer], All, *)
(*        {All, All, {AnalisiSintattica`Private`xy[*)
(*            AnalisiSintattica`Private`cursor] -> {Thick, Blue}}}], *)
(*      Background -> {White, White, White}, ItemStyle -> {Automatic}, *)
(*      ItemSize -> {{3, {5}}}, BaseStyle -> {Bold}], *)
(*    AnalisiSintattica`Private`solution = {{" ", "a", "b", "d", "f", "g", "l", *)
(*       "m", "$"}, {"A", "A->aB", "A->bC", " ", " ", " ", " ", " ", " "}, *)
(*      {"B", " ", " ", "B->d", "B->Ce", "B->Ce", " ", " ", " "}, *)
(*      {"C", " ", " ", " ", "C->fD", "C->gh ", " ", " ", " "}, *)
(*      {"D", " ", " ", " ", " ", " ", "D->l", "D->m", " "}}, *)
(*    AnalisiSintattica`Private`xy[AnalisiSintattica`Private`n_Integer] := *)
(*     {AnalisiSintattica`Private`row[AnalisiSintattica`Private`n], *)
(*      AnalisiSintattica`Private`col[AnalisiSintattica`Private`n]}, *)
(*    AnalisiSintattica`Private`xy[AnalisiSintattica`Private`n_] := *)
(*     {AnalisiSintattica`Private`row[AnalisiSintattica`Private`n], *)
(*      AnalisiSintattica`Private`col[AnalisiSintattica`Private`n]}, *)
(*    AnalisiSintattica`Private`row[AnalisiSintattica`Private`n_Integer] := *)
(*     Quotient[AnalisiSintattica`Private`n - 1, *)
(*       AnalisiSintattica`Private`cols] + 1, *)
(*    AnalisiSintattica`Private`row[AnalisiSintattica`Private`n_] := *)
(*     Quotient[AnalisiSintattica`Private`n - 1, *)
(*       AnalisiSintattica`Private`cols] + 1, AnalisiSintattica`Private`cols = *)
(*     9, AnalisiSintattica`Private`col[AnalisiSintattica`Private`n_Integer] := *)
(*     Mod[AnalisiSintattica`Private`n - 1, AnalisiSintattica`Private`cols] + *)
(*      1, AnalisiSintattica`Private`col[AnalisiSintattica`Private`n_] := *)
(*     Mod[AnalisiSintattica`Private`n - 1, AnalisiSintattica`Private`cols] + *)
(*      1, AnalisiSintattica`Private`createSol[*)
(*      AnalisiSintattica`Private`g_AnalisiSintattica`Private`solution] := *)
(*     AnalisiSintattica`Private`grammar, *)
(*    AnalisiSintattica`Private`createSol[AnalisiSintattica`Private`g:*)
(*       Blank[AnalisiSintattica`Private`createSol[*)
(*         {{" ", "a", "b", "d", "f", "g", "l", "m", "$"}, *)
(*          {"A", "A->aB", "A->bC", " ", " ", " ", " ", " ", " "}, *)
(*          {"B", " ", " ", "B->d", "B->Ce", "B->Ce", " ", " ", " "}, *)
(*          {"C", " ", " ", " ", "C->fD", "C->gh ", " ", " ", " "}, *)
(*          {"D", " ", " ", " ", " ", " ", "D->l", "D->m", " "}}]]] := *)
(*     AnalisiSintattica`Private`grammar, *)
(*    AnalisiSintattica`Private`createSol[AnalisiSintattica`Private`g:*)
(*       Blank[{{" ", "a", "b", "d", "f", "g", "l", "m", "$"}, *)
(*         {"A", "A->aB", "A->bC", " ", " ", " ", " ", " ", " "}, *)
(*         {"B", " ", " ", "B->d", "B->Ce", "B->Ce", " ", " ", " "}, *)
(*         {"C", " ", " ", " ", "C->fD", "C->gh ", " ", " ", " "}, *)
(*         {"D", " ", " ", " ", " ", " ", "D->l", "D->m", " "}}]] := *)
(*     AnalisiSintattica`Private`grammar, *)
(*    AnalisiSintattica`Private`createSol[AnalisiSintattica`Private`g_] := *)
(*     AnalisiSintattica`Private`grammar, AnalisiSintattica`Private`grammar = *)
(*     {{" ", "a", "b", "d", "f", "g", "l", "m", "$"}, *)
(*      {"A", "A->aB", "A->bC", " ", " ", " ", " ", " ", " "}, *)
(*      {"B", " ", " ", "B->d", "B->Ce", "B->Ce", " ", " ", " "}, *)
(*      {"C", " ", " ", " ", "C->fD", "C->gh ", " ", " ", " "}, *)
(*      {"D", " ", " ", " ", " ", " ", "D->l", "D->m", " "}}, *)
(*    AnalisiSintattica`Private`rows = 5, *)
(*    AnalisiSintattica`Private`loc[{AnalisiSintattica`Private`x_, *)
(*       AnalisiSintattica`Private`y_}] := *)
(*     1 + Floor[AnalisiSintattica`Private`cols*AnalisiSintattica`Private`x] + *)
(*      AnalisiSintattica`Private`cols*Floor[(1 - AnalisiSintattica`Private`y)**)
(*         AnalisiSintattica`Private`rows], AnalisiSintattica`Private`i = 5, *)
(*    AnalisiSintattica`Private`listaProduzioni = {"A->aB", "A->bC", "B->d", *)
(*      "B->Ce", "C->fD", "C->gh", "D->l", "D->m"}, *)
(*    AnalisiSintattica`Private`j = 2, AnalisiSintattica`Private`displaySln[*)
(*      AnalisiSintattica`Private`g_AnalisiSintattica`Private`solution] := *)
(*     AnalisiSintattica`Private`display[AnalisiSintattica`Private`g, 0], *)
(*    AnalisiSintattica`Private`displaySln[AnalisiSintattica`Private`g:*)
(*       Blank[AnalisiSintattica`Private`createSol[*)
(*         {{" ", "a", "b", "d", "f", "g", "l", "m", "$"}, *)
(*          {"A", "A->aB", "A->bC", " ", " ", " ", " ", " ", " "}, *)
(*          {"B", " ", " ", "B->d", "B->Ce", "B->Ce", " ", " ", " "}, *)
(*          {"C", " ", " ", " ", "C->fD", "C->gh ", " ", " ", " "}, *)
(*          {"D", " ", " ", " ", " ", " ", "D->l", "D->m", " "}}]]] := *)
(*     AnalisiSintattica`Private`display[AnalisiSintattica`Private`g, 0], *)
(*    AnalisiSintattica`Private`displaySln[AnalisiSintattica`Private`g:*)
(*       Blank[{{" ", "a", "b", "d", "f", "g", "l", "m", "$"}, *)
(*         {"A", "A->aB", "A->bC", " ", " ", " ", " ", " ", " "}, *)
(*         {"B", " ", " ", "B->d", "B->Ce", "B->Ce", " ", " ", " "}, *)
(*         {"C", " ", " ", " ", "C->fD", "C->gh ", " ", " ", " "}, *)
(*         {"D", " ", " ", " ", " ", " ", "D->l", "D->m", " "}}]] := *)
(*     AnalisiSintattica`Private`display[AnalisiSintattica`Private`g, 0], *)
(*    AnalisiSintattica`Private`displaySln[AnalisiSintattica`Private`g_] := *)
(*     AnalisiSintattica`Private`display[AnalisiSintattica`Private`g, 0], *)
(*    AnalisiSintattica`Private`createEmptyGrammar[*)
(*      AnalisiSintattica`Private`sln_Association] := *)
(*     Module[{AnalisiSintattica`Private`rows, AnalisiSintattica`Private`cols}, *)
(*      Table[AnalisiSintattica`Private`sln[AnalisiSintattica`Private`i, *)
(*         AnalisiSintattica`Private`j] = " ", {AnalisiSintattica`Private`i, 2, *)
(*        AnalisiSintattica`Private`rows}, {AnalisiSintattica`Private`j, 2, *)
(*        AnalisiSintattica`Private`cols}]], *)
(*    AnalisiSintattica`Private`createEmptyGrammar[*)
(*      AnalisiSintattica`Private`sln_] := *)
(*     Module[{AnalisiSintattica`Private`copy = AnalisiSintattica`Private`sln}, *)
(*      Table[If[AnalisiSintattica`Private`i > 1 && *)
(*          AnalisiSintattica`Private`j > 1, AnalisiSintattica`Private`copy[[*)
(*           AnalisiSintattica`Private`i,AnalisiSintattica`Private`j]] = " "], *)
(*        {AnalisiSintattica`Private`i, AnalisiSintattica`Private`rows}, *)
(*        {AnalisiSintattica`Private`j, AnalisiSintattica`Private`cols}]; *)
(*       AnalisiSintattica`Private`copy]}]*)


(* ::Input:: *)
(*Manipulate[Grid[{{Which[True, Style["Click on blank square:", "Label"]]}, *)
(*    {Column[{EventHandler[Dynamic[AnalisiSintattica`Private`display[*)
(*          AnalisiSintattica`Private`emptyGrammar, *)
(*          AnalisiSintattica`Private`cursor]], "MouseClicked" :> *)
(*         If[MemberQ[Range[1, AnalisiSintattica`Private`rows**)
(*              AnalisiSintattica`Private`cols, 9], *)
(*            AnalisiSintattica`Private`loc[MousePosition[*)
(*              "EventHandlerScaled"]]] || MemberQ[Range[2, *)
(*             AnalisiSintattica`Private`cols], AnalisiSintattica`Private`loc[*)
(*             MousePosition["EventHandlerScaled"]]], *)
(*          AnalisiSintattica`Private`cursor = -1, *)
(*          AnalisiSintattica`Private`cursor = AnalisiSintattica`Private`loc[*)
(*            MousePosition["EventHandlerScaled"]]]], *)
(*       Row[Table[With[{AnalisiSintattica`Private`i$ = *)
(*            AnalisiSintattica`Private`i}, Button[*)
(*           AnalisiSintattica`Private`listaProduzioni[[*)
(*            AnalisiSintattica`Private`i$]], *)
(*           AnalisiSintattica`Private`emptyGrammar[[*)
(*             AnalisiSintattica`Private`xy[AnalisiSintattica`Private`cursor][[*)
(*              1]],AnalisiSintattica`Private`xy[*)
(*               AnalisiSintattica`Private`cursor][[2]]]] = *)
(*            AnalisiSintattica`Private`listaProduzioni[[*)
(*             AnalisiSintattica`Private`i$]]]], {AnalisiSintattica`Private`i, *)
(*          1, Length[AnalisiSintattica`Private`listaProduzioni]}], *)
(*        Spacer[0.5]], Row[{Button["Clear", *)
(*          AnalisiSintattica`Private`emptyGrammar[[*)
(*            AnalisiSintattica`Private`xy[AnalisiSintattica`Private`cursor][[*)
(*             1]],AnalisiSintattica`Private`xy[*)
(*              AnalisiSintattica`Private`cursor][[2]]]] = " "], *)
(*         Button["Clear All", Table[AnalisiSintattica`Private`emptyGrammar[[*)
(*             AnalisiSintattica`Private`i,AnalisiSintattica`Private`j]] = " ", *)
(*           {AnalisiSintattica`Private`i, 2, AnalisiSintattica`Private`rows}, *)
(*           {AnalisiSintattica`Private`j, 2, *)
(*            AnalisiSintattica`Private`cols}]]}], *)
(*       If[AnalisiSintattica`Private`showSolution, *)
(*        Row[{AnalisiSintattica`Private`displaySln[*)
(*           AnalisiSintattica`Private`solution]}], ""]}, Alignment -> Center], *)
(*     " "}}], {{AnalisiSintattica`Private`solution, *)
(*    {{" ", "a", "b", "d", "f", "g", "l", "m", "$"}, *)
(*     {"A", "A->aB", "A->bC", " ", " ", " ", " ", " ", " "}, *)
(*     {"B", " ", " ", "B->d", "B->Ce", "B->Ce", " ", " ", " "}, *)
(*     {"C", " ", " ", " ", "C->fD", "C->gh ", " ", " ", " "}, *)
(*     {"D", " ", " ", " ", " ", " ", "D->l", "D->m", " "}}}, *)
(*   ControlType -> None}, {{AnalisiSintattica`Private`emptyGrammar, *)
(*    {{" ", "a", "b", "d", "f", "g", "l", "m", "$"}, *)
(*     {"A", " ", " ", " ", "A->bC", " ", " ", " ", " "}, *)
(*     {"B", " ", " ", " ", " ", " ", " ", " ", " "}, *)
(*     {"C", " ", " ", " ", " ", " ", " ", " ", " "}, *)
(*     {"D", " ", " ", " ", " ", " ", " ", " ", " "}}}, ControlType -> None}, *)
(*  {{AnalisiSintattica`Private`cursor, 14}, ControlType -> None}, *)
(*  Button["New Game", (AnalisiSintattica`Private`cursor = 0; *)
(*     AnalisiSintattica`Private`showSolution = False; *)
(*     AnalisiSintattica`Private`solution = AnalisiSintattica`Private`grammar; *)
(*     AnalisiSintattica`Private`emptyGrammar = *)
(*      AnalisiSintattica`Private`createEmptyGrammar[*)
(*       AnalisiSintattica`Private`solution]; ) & ], *)
(*  {{AnalisiSintattica`Private`showSolution, True, "show solution"}, *)
(*   {True, False}}, ContentSize -> {650, 420}, *)
(*  Initialization :> {AnalisiSintattica`Private`display[*)
(*      AnalisiSintattica`Private`g_AnalisiSintattica`Private`solution, *)
(*      AnalisiSintattica`Private`cursor_Integer:0] := *)
(*     Grid[AnalisiSintattica`Private`g, *)
(*      Frame -> If[MatchQ[AnalisiSintattica`Private`xy[*)
(*          AnalisiSintattica`Private`cursor], _Integer], All, *)
(*        {All, All, {AnalisiSintattica`Private`xy[*)
(*            AnalisiSintattica`Private`cursor] -> {Thick, Blue}}}], *)
(*      Background -> {White, White, White}, ItemStyle -> {Automatic}, *)
(*      ItemSize -> {{Automatic, {Automatic}}}, BaseStyle -> {Bold}], *)
(*    AnalisiSintattica`Private`display[AnalisiSintattica`Private`g_Null, *)
(*      AnalisiSintattica`Private`cursor_Integer:0] := *)
(*     Grid[AnalisiSintattica`Private`g, *)
(*      Frame -> If[MatchQ[AnalisiSintattica`Private`xy[*)
(*          AnalisiSintattica`Private`cursor], _Integer], All, *)
(*        {All, All, {AnalisiSintattica`Private`xy[*)
(*            AnalisiSintattica`Private`cursor] -> {Thick, Blue}}}], *)
(*      Background -> {White, White, White}, ItemStyle -> {Automatic}, *)
(*      ItemSize -> {{Automatic, {Automatic}}}, BaseStyle -> {Bold}], *)
(*    AnalisiSintattica`Private`display[AnalisiSintattica`Private`g:*)
(*       Blank[AnalisiSintattica`Private`createSol[*)
(*         {{" ", "a", "b", "d", "f", "g", "l", "m", "$"}, *)
(*          {"A", "A->aB", "A->bC", " ", " ", " ", " ", " ", " "}, *)
(*          {"B", " ", " ", "B->d", "B->Ce", "B->Ce", " ", " ", " "}, *)
(*          {"C", " ", " ", " ", "C->fD", "C->gh ", " ", " ", " "}, *)
(*          {"D", " ", " ", " ", " ", " ", "D->l", "D->m", " "}}]], *)
(*      AnalisiSintattica`Private`cursor_Integer:0] := *)
(*     Grid[AnalisiSintattica`Private`g, *)
(*      Frame -> If[MatchQ[AnalisiSintattica`Private`xy[*)
(*          AnalisiSintattica`Private`cursor], _Integer], All, *)
(*        {All, All, {AnalisiSintattica`Private`xy[*)
(*            AnalisiSintattica`Private`cursor] -> {Thick, Blue}}}], *)
(*      Background -> {White, White, White}, ItemStyle -> {Automatic}, *)
(*      ItemSize -> {{Automatic, {Automatic}}}, BaseStyle -> {Bold}], *)
(*    AnalisiSintattica`Private`display[AnalisiSintattica`Private`g:*)
(*       Blank[{{" ", "a", "b", "d", "f", "g", "l", "m", "$"}, *)
(*         {"A", "A->aB", "A->bC", " ", " ", " ", " ", " ", " "}, *)
(*         {"B", " ", " ", "B->d", "B->Ce", "B->Ce", " ", " ", " "}, *)
(*         {"C", " ", " ", " ", "C->fD", "C->gh ", " ", " ", " "}, *)
(*         {"D", " ", " ", " ", " ", " ", "D->l", "D->m", " "}}], *)
(*      AnalisiSintattica`Private`cursor_Integer:0] := *)
(*     Grid[AnalisiSintattica`Private`g, *)
(*      Frame -> If[MatchQ[AnalisiSintattica`Private`xy[*)
(*          AnalisiSintattica`Private`cursor], _Integer], All, *)
(*        {All, All, {AnalisiSintattica`Private`xy[*)
(*            AnalisiSintattica`Private`cursor] -> {Thick, Blue}}}], *)
(*      Background -> {White, White, White}, ItemStyle -> {Automatic}, *)
(*      ItemSize -> {Automatic}, BaseStyle -> {Bold}], *)
(*    AnalisiSintattica`Private`display[AnalisiSintattica`Private`g_, *)
(*      AnalisiSintattica`Private`cursor_:0] := *)
(*     Grid[AnalisiSintattica`Private`g, *)
(*      Frame -> If[MatchQ[AnalisiSintattica`Private`xy[*)
(*          AnalisiSintattica`Private`cursor], _Integer], All, *)
(*        {All, All, {AnalisiSintattica`Private`xy[*)
(*            AnalisiSintattica`Private`cursor] -> {Thick, Blue}}}], *)
(*      Background -> {White, White, White}, ItemStyle -> {Automatic}, *)
(*      ItemSize -> {{3, {5}}}, BaseStyle -> {Bold}], *)
(*    AnalisiSintattica`Private`solution = {{" ", "a", "b", "d", "f", "g", "l", *)
(*       "m", "$"}, {"A", "A->aB", "A->bC", " ", " ", " ", " ", " ", " "}, *)
(*      {"B", " ", " ", "B->d", "B->Ce", "B->Ce", " ", " ", " "}, *)
(*      {"C", " ", " ", " ", "C->fD", "C->gh ", " ", " ", " "}, *)
(*      {"D", " ", " ", " ", " ", " ", "D->l", "D->m", " "}}, *)
(*    AnalisiSintattica`Private`xy[AnalisiSintattica`Private`n_Integer] := *)
(*     {AnalisiSintattica`Private`row[AnalisiSintattica`Private`n], *)
(*      AnalisiSintattica`Private`col[AnalisiSintattica`Private`n]}, *)
(*    AnalisiSintattica`Private`xy[AnalisiSintattica`Private`n_] := *)
(*     {AnalisiSintattica`Private`row[AnalisiSintattica`Private`n], *)
(*      AnalisiSintattica`Private`col[AnalisiSintattica`Private`n]}, *)
(*    AnalisiSintattica`Private`row[AnalisiSintattica`Private`n_Integer] := *)
(*     Quotient[AnalisiSintattica`Private`n - 1, *)
(*       AnalisiSintattica`Private`cols] + 1, *)
(*    AnalisiSintattica`Private`row[AnalisiSintattica`Private`n_] := *)
(*     Quotient[AnalisiSintattica`Private`n - 1, *)
(*       AnalisiSintattica`Private`cols] + 1, AnalisiSintattica`Private`cols = *)
(*     9, AnalisiSintattica`Private`col[AnalisiSintattica`Private`n_Integer] := *)
(*     Mod[AnalisiSintattica`Private`n - 1, AnalisiSintattica`Private`cols] + *)
(*      1, AnalisiSintattica`Private`col[AnalisiSintattica`Private`n_] := *)
(*     Mod[AnalisiSintattica`Private`n - 1, AnalisiSintattica`Private`cols] + *)
(*      1, AnalisiSintattica`Private`createSol[*)
(*      AnalisiSintattica`Private`g_AnalisiSintattica`Private`solution] := *)
(*     AnalisiSintattica`Private`grammar, *)
(*    AnalisiSintattica`Private`createSol[AnalisiSintattica`Private`g:*)
(*       Blank[AnalisiSintattica`Private`createSol[*)
(*         {{" ", "a", "b", "d", "f", "g", "l", "m", "$"}, *)
(*          {"A", "A->aB", "A->bC", " ", " ", " ", " ", " ", " "}, *)
(*          {"B", " ", " ", "B->d", "B->Ce", "B->Ce", " ", " ", " "}, *)
(*          {"C", " ", " ", " ", "C->fD", "C->gh ", " ", " ", " "}, *)
(*          {"D", " ", " ", " ", " ", " ", "D->l", "D->m", " "}}]]] := *)
(*     AnalisiSintattica`Private`grammar, *)
(*    AnalisiSintattica`Private`createSol[AnalisiSintattica`Private`g:*)
(*       Blank[{{" ", "a", "b", "d", "f", "g", "l", "m", "$"}, *)
(*         {"A", "A->aB", "A->bC", " ", " ", " ", " ", " ", " "}, *)
(*         {"B", " ", " ", "B->d", "B->Ce", "B->Ce", " ", " ", " "}, *)
(*         {"C", " ", " ", " ", "C->fD", "C->gh ", " ", " ", " "}, *)
(*         {"D", " ", " ", " ", " ", " ", "D->l", "D->m", " "}}]] := *)
(*     AnalisiSintattica`Private`grammar, *)
(*    AnalisiSintattica`Private`createSol[AnalisiSintattica`Private`g_] := *)
(*     AnalisiSintattica`Private`grammar, AnalisiSintattica`Private`grammar = *)
(*     {{" ", "a", "b", "d", "f", "g", "l", "m", "$"}, *)
(*      {"A", "A->aB", "A->bC", " ", " ", " ", " ", " ", " "}, *)
(*      {"B", " ", " ", "B->d", "B->Ce", "B->Ce", " ", " ", " "}, *)
(*      {"C", " ", " ", " ", "C->fD", "C->gh ", " ", " ", " "}, *)
(*      {"D", " ", " ", " ", " ", " ", "D->l", "D->m", " "}}, *)
(*    AnalisiSintattica`Private`rows = 5, *)
(*    AnalisiSintattica`Private`loc[{AnalisiSintattica`Private`x_, *)
(*       AnalisiSintattica`Private`y_}] := *)
(*     1 + Floor[AnalisiSintattica`Private`cols*AnalisiSintattica`Private`x] + *)
(*      AnalisiSintattica`Private`cols*Floor[(1 - AnalisiSintattica`Private`y)**)
(*         AnalisiSintattica`Private`rows], AnalisiSintattica`Private`i = 5, *)
(*    AnalisiSintattica`Private`listaProduzioni = {"A->aB", "A->bC", "B->d", *)
(*      "B->Ce", "C->fD", "C->gh", "D->l", "D->m"}, *)
(*    AnalisiSintattica`Private`j = 2, AnalisiSintattica`Private`displaySln[*)
(*      AnalisiSintattica`Private`g_AnalisiSintattica`Private`solution] := *)
(*     AnalisiSintattica`Private`display[AnalisiSintattica`Private`g, 0], *)
(*    AnalisiSintattica`Private`displaySln[AnalisiSintattica`Private`g:*)
(*       Blank[AnalisiSintattica`Private`createSol[*)
(*         {{" ", "a", "b", "d", "f", "g", "l", "m", "$"}, *)
(*          {"A", "A->aB", "A->bC", " ", " ", " ", " ", " ", " "}, *)
(*          {"B", " ", " ", "B->d", "B->Ce", "B->Ce", " ", " ", " "}, *)
(*          {"C", " ", " ", " ", "C->fD", "C->gh ", " ", " ", " "}, *)
(*          {"D", " ", " ", " ", " ", " ", "D->l", "D->m", " "}}]]] := *)
(*     AnalisiSintattica`Private`display[AnalisiSintattica`Private`g, 0], *)
(*    AnalisiSintattica`Private`displaySln[AnalisiSintattica`Private`g:*)
(*       Blank[{{" ", "a", "b", "d", "f", "g", "l", "m", "$"}, *)
(*         {"A", "A->aB", "A->bC", " ", " ", " ", " ", " ", " "}, *)
(*         {"B", " ", " ", "B->d", "B->Ce", "B->Ce", " ", " ", " "}, *)
(*         {"C", " ", " ", " ", "C->fD", "C->gh ", " ", " ", " "}, *)
(*         {"D", " ", " ", " ", " ", " ", "D->l", "D->m", " "}}]] := *)
(*     AnalisiSintattica`Private`display[AnalisiSintattica`Private`g, 0], *)
(*    AnalisiSintattica`Private`displaySln[AnalisiSintattica`Private`g_] := *)
(*     AnalisiSintattica`Private`display[AnalisiSintattica`Private`g, 0], *)
(*    AnalisiSintattica`Private`createEmptyGrammar[*)
(*      AnalisiSintattica`Private`sln_Association] := *)
(*     Module[{AnalisiSintattica`Private`rows, AnalisiSintattica`Private`cols}, *)
(*      Table[AnalisiSintattica`Private`sln[AnalisiSintattica`Private`i, *)
(*         AnalisiSintattica`Private`j] = " ", {AnalisiSintattica`Private`i, 2, *)
(*        AnalisiSintattica`Private`rows}, {AnalisiSintattica`Private`j, 2, *)
(*        AnalisiSintattica`Private`cols}]], *)
(*    AnalisiSintattica`Private`createEmptyGrammar[*)
(*      AnalisiSintattica`Private`sln_] := *)
(*     Module[{AnalisiSintattica`Private`copy = AnalisiSintattica`Private`sln}, *)
(*      Table[If[AnalisiSintattica`Private`i > 1 && *)
(*          AnalisiSintattica`Private`j > 1, AnalisiSintattica`Private`copy[[*)
(*           AnalisiSintattica`Private`i,AnalisiSintattica`Private`j]] = " "], *)
(*        {AnalisiSintattica`Private`i, AnalisiSintattica`Private`rows}, *)
(*        {AnalisiSintattica`Private`j, AnalisiSintattica`Private`cols}]; *)
(*       AnalisiSintattica`Private`copy]}]*)
=======
Manipulate[
	Grid[
	{{Column[{Style["ANALISI SINTATTICA", Bold],
	  Style["ESERCIZIO DI GRAMMATICA N\[Degree]:", Bold] (*INSERISCI SEED*),
	  Style["Generare gli insiemi Nullable, First e Follow per la seguente grammatica", Bold] }, 
	  Alignment -> Center]},
	{
	Column[{
		(*GRAMMATICA*)
		Row[{
		
		Button["Nuova grammatica",(
		cursor=0 ; 
		Spacer[5];
		showSolution=False;
		soluzione=grammar;
		emptyGrammar=createEmptyGrammar[soluzione];
		)&],
		
		DynamicModule[{numero = ""}, 
        Panel[Column[{
        Row[{
        Style["Genera esercizio n\[Degree]: ", Bold],
        InputField[Dynamic[numero], Number]
        }],
        Dynamic[numero];
        }]]
	    ]}], " ",
		Row[{Column[{
			Style["Grammatica", Bold],
			Grid[Map[List, listaProduzioni],
			 Frame -> All, 
			 Background->{White,White},
			 ItemStyle->{Automatic},
			 ItemSize->{{8,{8}}},
		     BaseStyle->{Bold}
			 Editable -> False]}, Alignment->Center]}], 
			" ",
			
		(*NULLABLE*)
		Row[{Column[{
			Style["NULLABLE", Bold],
			TabView[Table[tmp[[i]]->PopupMenu[" ",{TRUE, FALSE}],{i, 1, Length[tmp]}]]}, Alignment->Left],
			" "		 
          }], 
			" ",
			
		(*FIRST*)	
		Row[{Column[{
			Style["FIRST", Bold],
			displayFirstFollow[emptyCheckboxGrammar]
			}, Alignment->Left]		 
          }], 
        
		(*TABLE*)	
		EventHandler[
			Dynamic[display[emptyGrammar,cursor]],
			"MouseClicked":>(
			If[MemberQ[Range[1, rows*cols, cols],loc[MousePosition["EventHandlerScaled"]]] || 
				MemberQ[Range[1, cols],loc[MousePosition["EventHandlerScaled"]]],
				cursor = -1,
				cursor = loc[MousePosition["EventHandlerScaled"]]
				] 
			)], 
	Row[  
		Table[With[{i = i},\[NonBreakingSpace]
\[NonBreakingSpace]       Button[listaProduzioni[[i]],
\[NonBreakingSpace]              emptyGrammar[[xy[cursor][[1]], xy[cursor][[2]]]]=listaProduzioni[[i]];
\[NonBreakingSpace]              (*MessageDialog["Hai sbagliato"]*) 
\[NonBreakingSpace]       ]], 
\[NonBreakingSpace]       {i, 1, Length[listaProduzioni]}],Spacer[0.5]     
\[NonBreakingSpace]           
    ],
    Row[{
        Button["Clear", emptyGrammar[[xy[cursor][[1]], xy[cursor][[2]]]]= " "],
        Button["Clear All", Table[emptyGrammar[[i,j]] = " ", {i, 2, rows}, {j, 2, cols}]]
        }],
      
    (*rimuovi puntatore da tabella soluzione *)
    If[showNullable, Column[{
						Style["Mostra Nullable", Bold],
						TabView[Table[tmp[[i]]->nullable[[i,2]],{i, 1, Length[tmp]}]]}, Alignment->Right]," "],
	If[showFirst, Column[{
						Style["Mostra First", Bold],
						displayFirstFollowSln[emptyCheckboxGrammar]
						},Alignment->Right],""],					
    If[showSolution,Row[{displaySln[soluzione]}],""]
    },
    Alignment -> Center
    ],
   
	" "	
	}
	}],
	{soluzione,ControlType->None},
	{first,ControlType->None},
	{{emptyGrammar, (soluzione=grammar;createEmptyGrammar[soluzione])},ControlType->None},
	{{emptyCheckboxGrammar, (soluzione;createEmptyCheckbox[soluzione])},ControlType->None},
	{{cursor,0},ControlType->None},
   
	(*Genera nuova gramm con seed da keyboard*)
	{{showNullable,False,"Mostra Nullable"},{True,False}},
	{{showFirst,False,"Mostra First"},{True,False}},
	{{showSolution,False,"show solution"},{True,False}},
	SaveDefinitions->True,
	ContentSize->{900, 900}
]




>>>>>>> Stashed changes


End[]


EndPackage[]
