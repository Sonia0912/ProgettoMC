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


BeginPackage["AnalisiSintattica`"];


(* ::Input:: *)
(*(*Funzioni private del pacchetto*)*)
(*Remove[GenerazioneGrammatica]*)
(*Remove[GenerazioneListaProduzioni]*)
(*Remove[GenerazioneNullable]*)
(*Remove[GenerazioneFirst]*)
(*Remove[GenerazioneFollow]*)
(*Remove[GenerazioneSoluzione]*)
(*Remove[GenerazioneInterfaccia]*)
(*Remove[getFirst]*)
(*Remove[checkNullabilita]*)
(*Remove[inserisciProduzione]*)
(*Remove[rimuoviNTeEps]*)
(*Remove[Global`GenerazioneEsercizio]*)
(*Remove[displayGrammatica]*)
(*Remove[displayNullable]*)
(*Remove[displayNullableSln]*)
(*Remove[displayFirstFollow]*)
(*Remove[displayFirstFollowSln]*)
(*Remove[displayTable]*)
(*Remove[displayTableSln]*)
(*Remove[checkErrors]*)
(*Remove[createEmptyNullableCheckbox]*)
(*Remove[createEmptyFirstFollowCheckbox]*)
(*Remove[createEmptyGrammar]*)
(*Remove[loc]*)
(*Remove[row]*)
(*Remove[col]*)
(*Remove[xy]*)
(**)


GenerazioneEsercizio::usage:= 
"GenerazioneEsercizio[seed] crea l'interfaccia su cui svolgere l'esercizio con il seed dato (seed = 0 usa un seed casuale)";


Begin["`Private`"];


(*GENERAZIONE GRAMMATICA CASUALE
- A ogni Non Terminale (sempre A, B, C, D) e' associata una lista composta da Terminali e da Non Terminali.
- Questa lista viene poi suddivisa in 1/2/3 produzioni che saranno associate a quel non terminale.
- Tutti gli elementi della lista devono apparire esattamente una volta nelle produzioni.
- Esempio:
A: a, b, B
B: c, d, C
C: e, f, D
D: g, h
*)
GenerazioneGrammatica[] := (
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
)


(*Riscrive la grammatica con il formato "NT -> produzione"*)
GenerazioneListaProduzioni[] := (
	listaProduzioni = List[];
	Table[
		Table[
			AppendTo[listaProduzioni, StringJoin[grammatica[[i, 1]], "->", grammatica[[i, 2, j]]]];
		,{j, 1, Length[grammatica[[i, 2]]]}
		];
	,{i, 1, Length[grammatica]}
	];
	listaProduzioni
)


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

GenerazioneNullable[] := (
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
)


(* FIRST *)

GenerazioneFirst[] := ( 
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
)


(* FOLLOW *)

GenerazioneFollow[] := ( 
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
)


(*GENERAZIONE DELLA SOLUZIONE*)

GenerazioneSoluzione[] := ( 
	soluzione = List[];
	
	colonne = tuttiTerminali;
	colonne = Prepend[colonne, " "];
	AppendTo[colonne, "$"];
	numColonne = Length[colonne];
	AppendTo[soluzione, colonne];
	
	rigaCorrente = List[];
	
	Table[	
		(*Inizializziamo la riga di quel Non Terminale*)
		Table[
			AppendTo[rigaCorrente, " "];,
			{h, 1, numColonne}
		];
		(*Il primo elemento della riga sara' il NT corrente*)
		rigaCorrente = ReplacePart[rigaCorrente, 1 -> tuttiNonTerminali[[i]]];
		AppendTo[soluzione, rigaCorrente];
		
		(*Cicliamo su tutte le produzioni del NT corrente*)
		Table[
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
			];,
			{j, 1, Length[grammatica[[i,2]]]}
		];
		
		(*Reinizializziamo rigaCorrente*)
		Clear[rigaCorrente];
	    rigaCorrente = List[];,
	    {i, 1, numNonTerminali}
	];
	
	soluzione
	)


(*Funzione che mostra la grammatica generata in una griglia*)
displayGrammatica[g_] :=\[NonBreakingSpace]
	Module[{grammar = g, formattedList},\[NonBreakingSpace]formattedList =\[NonBreakingSpace]Map[{#[[1]] <> " -> " <> StringRiffle[#[[2]], " | "]} &, grammar];
\[NonBreakingSpace]   Grid[formattedList, Frame -> All, Background -> {White, White},\[NonBreakingSpace]
\[NonBreakingSpace]\[NonBreakingSpace]  ItemStyle -> {17,17}, 
\[NonBreakingSpace]\[NonBreakingSpace]  ItemSize -> {Automatic,2},\[NonBreakingSpace]
\[NonBreakingSpace]\[NonBreakingSpace]  Alignment -> Left,
\[NonBreakingSpace]\[NonBreakingSpace]  BaseStyle -> {Bold}, 
\[NonBreakingSpace]\[NonBreakingSpace]  Editable -> False]]
\[NonBreakingSpace]
(*Funzione che prende in input la lista dei simboli nullable e li stampa in una griglia*)
displayNullable[g_]:=Grid[g,
			 Frame -> All, 
			 Background->{White,White},
			 ItemStyle->{Automatic},
			 ItemSize->{{4,{4}}},
		     BaseStyle->{Bold},
			 Editable -> False]

(*Funzione che prende in input la lista dei simboli First o dei simboli Follow e li stampa in una griglia*)
displayFirstFollow[g_]:=Grid[g,
			 Frame -> All, 
			 Background->{White,White},
			 ItemStyle->{Automatic},
			 ItemSize->{{4,{4}}},
		     BaseStyle->{Bold},
			 Editable -> False]
					
(*Funzione che prende in input la grammatica e stampa la griglia.
Pu\[OGrave] prendere in input anche un cursore che evidenzia di blu la cella cliccata dall'utente*)		
displayTable[g_,cursor_:0]:=
	(Module[{backgrounds},
		backgrounds = checkErrors[g];
		Grid[g,
		Frame->If[MatchQ[xy[cursor],_Integer],All,{All,All,{xy[cursor]->{Thick,Blue}}}],
		Background->{White, White, backgrounds},
		ItemStyle->{Automatic},
		ItemSize->{{3,{4}}},
		BaseStyle->{Bold},
		Editable -> False]])

(*Funzione che prende in input la grammatica e la stampa con le produzioni nelle posizione corrette*)	
displayTableSln[g_]:=(displayTable[g,0])

(*Funzione che controlla la singola produzione inserita dall'utente. 
In caso essa non corrisponda a quella esatta della soluzione, viene colorata la cella di rosso.*)
checkErrors[g_]:=
	(
	tmp = List[];
	cond = True;
	Table[ 
	(*le metto tutte a lightblue, se indivua errore cambio colore*)
		If[g[[xy[i][[1]], xy[i][[2]]]] != " ", 
\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]        If[ g[[xy[i][[1]], xy[i][[2]]]]!= soluzione[[xy[i][[1]], xy[i][[2]]]],
\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]   AppendTo[tmp, xy[i]-> LightRed]];
\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]   cond = False;
\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]  ];
\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]If[cond,AppendTo[tmp, xy[i]-> White ]];
\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace] , {i,1,rows*cols}];
\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace] 
\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace] tmp
\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace])
\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace] 
(*Crea la tabella nullable vuota*)\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace] 
\[NonBreakingSpace]createEmptyNullableCheckbox[sln_]:= 
	(Module[{copy = sln}, Table[copy[[i, 2]] = Checkbox[], {i, 1, rows-1}]; copy ])\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]
\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace] \[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace] 
(*Crea la tabella vuota con celle checkbox per i First e Follow*)
createEmptyFirstFollowCheckbox[sln_,tabFirst_]:=\[NonBreakingSpace]
\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace] (Module[{copy = sln}, Table[ If[i > 1 && j > 1, copy[[i, j]] = Checkbox[]], {i, rows}, {j, cols} ];
\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace] If[tabFirst,copy[[1,cols]] = "\[Epsilon]"; ];
\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace] copy ])\[NonBreakingSpace]
\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace] \[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace] \[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace] \[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace] \[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace] \[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace] \[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace] 
(*Crea la tabella finale delle produzioni vuota*)
createEmptyGrammar[sln_]:= 
	(Module[{copy = sln}, Table[ If[i > 1 && j > 1, copy[[i, j]] = " "], {i, rows}, {j, cols} ]; copy] )

(*Funzione che prende in input le coordinate corrispondenti alla posizione del mouse 
e restituisce un intero settato sulla dimensione della griglia*)
loc[{x_, y_}] := 1 + Floor[cols x] + cols Floor[(1 - y) rows];

(*Funzione che calcola l'esatta riga e colonna di ogni cella della tabella*)
row[n_]:=(Quotient[n-1,cols]+1);
col[n_]:=(Mod[n-1,cols]+1);

(*Funzione che presa in input una cella della griglia ne restituisce riga e colonna corrispondenti*)
xy[n_]:=({row[n],col[n]});

(*Funzione che preso in input un seed genera la manipulate*)
GenerazioneInterfaccia[seed_]:=(
showNullable=False;
showFirst=False;
showFollow=False;
showSolution=False;
num = seed;

interface=Manipulate[
	Grid[
	{{
	
       Column[{
       Style["ANALISI SINTATTICA", Bold, FontSize -> 28], " ",
       Style["ESERCIZIO DI GRAMMATICA N\[Degree]:"<>ToString[num], Bold, FontSize -> 20]
     }, Alignment -> Center]
    },
	{
	  Column[{
		" ",
		Row[{
		Style["Generare gli insiemi Nullable, First e Follow per la seguente grammatica", Bold, FontSize -> 15]},
	    Alignment->Left],
	    " ",
		Row[{
		Button["Nuovo Esercizio",(
		cursor=0 ; 
		Spacer[5];
		ImageSize->{100,100};
		emptyGrammar = createEmptyGrammar[soluzione];
		(*Al clic del bottone viene generata una nuova grammatica con seed random*)
		GenerazioneEsercizio[];
		)],
		" ", " ",
		DynamicModule[{parametro = ""},
        Row[{
        Row[{
        Style["oppure ripeti l'esercizio n\[Degree]:", Bold],
        Spacer[1],
        (*Input field in cui inserire un valore positivo fra 1 e 10000 per generare un esercizio con uno specifico seed*)
        InputField[Dynamic[parametro, If[NumberQ[#],parametro = Abs[#]]&], Number,  ImageSize -> {100,20}]
        }],
        Button["Genera", 
        If[parametro != "" && 0<=parametro<=10000, 
           cursor=0 ;
           emptyGrammar = createEmptyGrammar[soluzione];
           (*Al clic del bottone viene generata una nuova grammatica con seed preso da tastiera*)
           GenerazioneEsercizio[parametro];,
           MessageDialog["Inserire un valore compreso fra 1 e 10000"]];
        ]
        }]
        ]
		}], 
		" ",
		Row[{Column[{
			Style["GRAMMATICA", Bold, FontSize->17],
			displayGrammatica[grammatica]}, Alignment->Left]}], 
		" ",	
		(*NULLABLE*)
		Row[{Column[{
			Style["NULLABLE", Bold, FontSize->17],
			Framed["Dato un non terminale, questo \[EGrave] nullable se pu\[OGrave] produrre una stringa vuota (\[Epsilon]).\nSeleziona i non terminali nullable.",
					FrameStyle -> Directive[Thin, White], ImageSize -> {Automatic}, Alignment -> Top],	
			displayNullable[emptyNullableCheckbox],
			" ",
			(*Al clic del bottone viene mostrata la tabella con la soluzione per i simboli Nullable*)
			Button["Mostra Soluzione Nullable",
            showNullable = Not[showNullable],ImageSize->{Automatic}
            ], " ",         
			Dynamic[If[showNullable, 
				Column[{
						Style["Soluzione Nullable", Bold],
						displayNullable[nullable]}, Alignment->Left]," "]]
			}, Alignment->Left]," "
					 
          }], 
			" ",
			
		(*FIRST*)	
		Row[{Column[{
			Style["FIRST", Bold, FontSize->17],
			Framed["Dato un non terminale (ad esempio A,B), il suo insieme First \[EGrave] composto dai simboli terminali (compreso \[Epsilon])\nche possono apparire come carattere iniziale di una stringa derivata da una sua produzione.",
					FrameStyle -> Directive[Thin, White], ImageSize -> {Automatic}, Alignment -> Top], 
			displayFirstFollow[emptyFirstCheckbox], 			
			" ",	
			(*Al clic del bottone viene mostrata la tabella con la soluzione per i simboli First*)	
			Button["Mostra Soluzione First",
            showFirst = Not[showFirst],ImageSize->{Automatic}
            ], " ",
            Dynamic[If[showFirst, 
				Column[{
					Style["Soluzione First", Bold],
					displayFirstFollow[first]					
				},
				Alignment->Left],""]] 			
			}, Alignment->Left]					 
          }],  
          " ",
          
          (*FOLLOW*)	
		Row[{Column[{
			Style["FOLLOW", Bold, FontSize->17],
			Framed["Dato un non terminale, il suo insieme Follow \[EGrave] composto dai simboli terminali (e dal simbolo $)\nche possono apparire immediatamente dopo il non terminale in qualsiasi derivazione valida.",
					FrameStyle -> Directive[Thin, White], ImageSize -> {Automatic}, Alignment -> Top],
	        displayFirstFollow[emptyFollowCheckbox],
			" ",
			(*Al clic del bottone viene mostrata la tabella con la soluzione per i simboli Follow*)
			Button["Mostra Soluzione Follow",
            showFollow = Not[showFollow], ImageSize->{Automatic}]
            , " ",
			Dynamic[If[showFollow, 
				Column[{
					Style["Soluzione Follow", Bold],
					displayFirstFollow[follow]
				},Alignment->Left],""]]
			}, Alignment->Left]	 
          }], 
         " ",
         
		(*TABLE*)	
		Row[{
			Column[{
			Style["TABELLA PRODUZIONI", Bold, FontSize->17],
			Framed["Seleziona la cella in cui inserire la produzione e successivamente il bottone ad essa corrispondente.",
					FrameStyle -> Directive[Thin, White],ImageSize -> {Automatic}, Alignment -> Top],
			EventHandler[
			Dynamic[displayTable[emptyGrammar,cursor]],
			(*MouseClicked permette di calcolare tramite la funzione loc la posizione del mouse.
			Controlla che l'utente non modifichi le intestazioni della tabella in cui sono presenti Terminali e Non terminali.
			In caso contrario setta il cursore a -1.*)
			"MouseClicked":>(
			If[MemberQ[Range[1, rows*cols, cols],loc[MousePosition["EventHandlerScaled"]]] || 
				MemberQ[Range[1, cols],loc[MousePosition["EventHandlerScaled"]]],
				cursor = -1,
				cursor = loc[MousePosition["EventHandlerScaled"]]
				] 
			)],
			Row[ 
			(*Viene creata una serie di bottoni ciascuno indicante una delle produzioni della grammatica generata.*)
			Table[With[{i = i},\[NonBreakingSpace]
\[NonBreakingSpace]           Button[listaProduzioni[[i]],
\[NonBreakingSpace]           If[cursor > 0,
\[NonBreakingSpace]              emptyGrammar[[xy[cursor][[1]], xy[cursor][[2]]]]=listaProduzioni[[i]];
\[NonBreakingSpace]              
\[NonBreakingSpace]              (*Controllo che la produzione inserita nella cella sia nella posizione corretta.
\[NonBreakingSpace]              In caso contrario viene eseguito un Beep.*)
\[NonBreakingSpace]              If[emptyGrammar[[xy[cursor][[1]], xy[cursor][[2]]]] != soluzione[[xy[cursor][[1]], xy[cursor][[2]]]], Beep[]]
\[NonBreakingSpace]            ];
\[NonBreakingSpace]            ]], 
\[NonBreakingSpace]            {i, 1, Length[listaProduzioni]}],Spacer[0.4]
            ],
            Row[{
            (*Bottone che permette di svuotare il contenuto di una singola cella*)
            Button["Svuota", 
            If[cursor > 0,
            emptyGrammar[[xy[cursor][[1]], xy[cursor][[2]]]]= " "]
            ]
            , " ",
            (*Bottone che permette di svuotare il contenuto dell'intera griglia*)
            Button["Svuota Tutto", Table[emptyGrammar[[i,j]] = " ", {i, 2, rows}, {j, 2, cols}]],  " "        
            }, Alignment -> Center],
            " ",
            (*Al clic del bottone viene mostrata la tabella con la soluzione finale della tabella di Parsing*)
            Button["Mostra Soluzione Tabella",
            showSolution = Not[showSolution],
            ImageSize->{Automatic}
            ], " ",
            Dynamic[If[showSolution, 
				Column[{Style["Soluzione tabella delle produzioni", Bold],
				displayTableSln[soluzione]},Alignment -> Left],""]] 
			}]
			}, Alignment->Center], " "
    }], 
	" "}
	}, Editable->False],
	{{emptyNullableCheckbox, createEmptyNullableCheckbox[nullable]},ControlType->None},
	{{emptyFirstCheckbox, createEmptyFirstFollowCheckbox[soluzione, True]},ControlType->None},
	{{emptyFollowCheckbox, createEmptyFirstFollowCheckbox[soluzione, False]},ControlType->None},
	{{emptyGrammar, createEmptyGrammar[soluzione]},ControlType->None},
	{{cursor,0},ControlType->None},

	SaveDefinitions->True,
	ContentSize->{Automatic}
];
interface)


(*Funzione globale che permette di eseguire l'intero esercizio*)
GenerazioneEsercizio[seed_:0] := (
	numEsercizio = seed;
	
	(*Controllo che il seed sia un valore intero compreso fra 0 e 10000*)
	If[NumberQ[numEsercizio] && 0<=numEsercizio<=10000, 		            
	(*Se il seed non viene specificato \[EGrave] preso randomicamente*)
	If[numEsercizio == 0,
		numEsercizio = RandomInteger[{1,9999}];
		SeedRandom[numEsercizio];
	,
		SeedRandom[numEsercizio];
	];
	
	grammatica = GenerazioneGrammatica[];
	listaProduzioni = GenerazioneListaProduzioni[];
	nullable = GenerazioneNullable[];
	first = GenerazioneFirst[];
	follow = GenerazioneFollow[];
	soluzione = GenerazioneSoluzione[];

	rows = Length[soluzione[[All,1]]];
	cols = Length[soluzione[[1, All]]];
	interfaccia = GenerazioneInterfaccia[numEsercizio];,
	MessageDialog["Inserire un valore compreso fra 1 e 10000"]];
	
	interfaccia
	)


End[];


EndPackage[];
