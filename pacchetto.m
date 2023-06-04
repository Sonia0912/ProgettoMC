(* ::Package:: *)

(* :Title: Esercizio Analisi Sintattica *)
(* :Context: AnalisiSintattica` *)
(* :Author: Lorenzo Campidelli, Luca Castricini, Gianluca Gueli, Sonia Nicoletti, Anna Tosoroni *)
(* :Summary: Pacchetto che permette la generazioni di esercizi sull'analisi sintattica *)
(* :Copyright: GS 2023 *)
(* :Package Version: 1 *)
(* :Mathematica Version: 13.2 *)
(* :History: last modified 22/05/2023 *)
(* :Keywords: analisi sintattica, compilatori, interpreti, grammatica *)
(* :Sources: https://reference.wolfram.com/language/, https://www.demonstrations.wolfram.com/PlayableSudokuGame/*)
(* :Limitations: this is a preliminary version, for educational purposes only. *)
(* :Discussion: Abbiamo seguito l'implementazione dell'interfaccia del sudoku adattandola al nostro esercizio. *)
(* :Requirements: Mathematica Version 13*)


BeginPackage["AnalisiSintattica`"]


GenerazioneEsercizio::usage := 
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

GenerazioneGrammatica[] := 
	Module[{},	
		(*Parametri per la generazione*)
		tuttiNonTerminali = CharacterRange["A", "D"]; (*simboli Non Terminali disponibili*)
		tuttiTerminali = CharacterRange["a", "l"];    (*simboli terminali disponibli*)
		
		
		numNonTerminali = Length[tuttiNonTerminali];
		numTerminali = Length[tuttiTerminali];
		
		(*parametri per la lunghezza delle produzioni*)
		maxNumeroNonTerminali = 2;
		minNumeroTerminali = 2;
		maxNumeroTerminali = 3;
		maxProduzioni = 4; 
		
		probabilitaEpsilon = 40; (*probabilita' che compaia Epsilon come produzione per un Non Terminale*)
		
		(*Inizializzazione lista per la grammatica finale*)
		Clear[grammatica];
		grammatica = List[];
		
		(*liste da consumare per generare la grammatica*)
		nonTerminali = tuttiNonTerminali;
		nonTerminali = Drop[nonTerminali, 1];
		nonTerminaliIndici = tuttiNonTerminali;
		terminali = tuttiTerminali;
		
		(*Per ogni Non Terminale viene generata la sua lista di produzioni*)
		Table[
		  	(*Salva il primo Non Terminale in una lista e lo rimuove dalla lista nonTerminali*)
		  	Clear[listaNonTerminaleEProduzioni];
		  	listaNonTerminaleEProduzioni = List[];
		  	AppendTo[listaNonTerminaleEProduzioni, nonTerminaliIndici[[1]]];
		  	nonTerminaliIndici = Drop[nonTerminaliIndici, 1];
		  	
		  	numNonTerminaliRimanenti = Length[nonTerminali];
		  	
		  	(*Creazione della stringa di tutte le produzioni per il Non Terminale corrente*)
		  	If[numNonTerminaliRimanenti > 0, 
		   		(*Ci sono ancora Non Terminali inutilizzati*)
		   		(*seleziona un numero casuale di Terminali e Non Terminali e li rimuove dalle rispettive liste*)
		   		numElementiNonTerminali = RandomInteger[{1, Min[maxNumeroNonTerminali, numNonTerminaliRimanenti]}];
		   		elementiNonTerminali = nonTerminali[[1 ;; numElementiNonTerminali]];
		   		nonTerminali = Drop[nonTerminali, numElementiNonTerminali];
		   		numElementiTerminali = RandomInteger[{minNumeroTerminali, maxNumeroTerminali}];
		   		elementiTerminali = terminali[[1 ;; numElementiTerminali]];
		   		terminali = Drop[terminali, numElementiTerminali];
		   		,
		   		(*Sono stati usati tutti i Non terminali*)	
		   		(*seleziona un numero casuale di Terminali e li rimuove dalla lista*)
		   		numElementiTerminali = RandomInteger[{minNumeroTerminali, maxNumeroTerminali}];
		   		elementiTerminali = terminali[[1 ;; numElementiTerminali]];
		   	    terminali = Drop[terminali, numElementiTerminali];
		   		elementiNonTerminali = List[];
		   	];
		   	(*viene creata una stringa casuale di caratteri che andranno a formare le produzioni*)
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
	]


(*Riscrive la grammatica con il formato "NT -> produzione"*)
GenerazioneListaProduzioni[] := 
	Module[{},
		listaProduzioni = List[];
		Table[ (*per ogni Non Terminale della grammatica*)
			Table[ (*per ogni produzione del Non Terminale*)
				(*inserisce in una lista la stringa "NT -> produzione"*)
				AppendTo[listaProduzioni, StringJoin[grammatica[[i, 1]], "->", grammatica[[i, 2, j]]]];
			,{j, 1, Length[grammatica[[i, 2]]]}
			];
		,{i, 1, Length[grammatica]}
		];
		listaProduzioni
	]


(*FUNZIONI AUSILIARIE*)

(*Ritorna i First di un Non Terminale*)
getFirst[NT0_] :=
	Module[{NT = NT0},
		posizione = Position[first,NT];
		posizioneFlat = Flatten[posizione];
		firstNT = first[[posizioneFlat[[1]],2]];
		firstNT	
	]

(*Ritorna True se il Non Terminale e' nullable, False se non e' nullable*)
checkNullabilita[NT1_] := 
	Module[{NT = NT1}, 
		posNTinNullable = Position[nullable, NT];
		indiceNTinNullable = posNTinNullable[[1, 1]];
		nullabilita = nullable[[indiceNTinNullable,2]];
		nullabilita
	]

(*Data una produzione, le colonne e la riga in cui inserirla, la inserisce nella soluzione*)
inserisciProduzione[prod0_, colonne0_, riga0_] := 
	Module[{prod = prod0, colonne = colonne0, riga = riga0}, 
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
	]

(*Ritorna una lista di Terminali rimouvendo, se ci sono, Non Terminali e \[Epsilon]*)
rimuoviNTeEps[lista0_] := 
	Module[{lista = lista0}, 
		nuovaLista = lista;
		Table[
			If[ContainsAny[{nuovaLista[[k]]},tuttiNonTerminali] || ContainsAny[{nuovaLista[[k]]},{"\[Epsilon]"}],
				nuovaLista = Drop[nuovaLista, {k}];
			];
			,
			{k, 1, Length[nuovaLista], 1}
		];
		nuovaLista
	]


(* NULLABLE *)

GenerazioneNullable[] := 
	Module[{},
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
	]


(* FIRST *)

GenerazioneFirst[] := 
	Module[{},
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
	]


(* FOLLOW *)

GenerazioneFollow[] := 
	Module[{},
		follow = {{"A", {"$"}}};
		listaRicontrollo1 = List[];
		listaRicontrollo2 = List[];
		
		(*Inizializzazione lista di Follow*)
		Table[
			AppendTo[follow, {tuttiNonTerminali[[i]], {}}]
		,{i, 2, numNonTerminali}
		];
		
		(*Itera su tutte le produzioni di tutti i Non Terminali*)
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
		
		(*Riordinamento e rimozione degli eventuali caratteri ripetuti*)
		Table[
			follow[[i, 2]] = Flatten[follow[[i, 2]]];
			DeleteDuplicates[follow[[i, 2]]];
			Sort[follow[[i, 2]]];
		,{i, 1, Length[follow]}	
		];
		
		follow
	]


(*GENERAZIONE DELLA SOLUZIONE*)

GenerazioneSoluzione[] := 
	Module[{},
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
	]


(*Funzione che mostra la grammatica generata in una griglia*)
displayGrammatica[g_] :=\[NonBreakingSpace]
	Module[{grammar = g, formattedList},\[NonBreakingSpace]
		formattedList =\[NonBreakingSpace]Map[{#[[1]] <> " -> " <> StringRiffle[#[[2]], " | "]} &, grammar];
	\[NonBreakingSpace]   Grid[formattedList, Frame -> All, Background -> {White, White},\[NonBreakingSpace]
	\[NonBreakingSpace]\[NonBreakingSpace]  ItemStyle -> {17,17}, 
	\[NonBreakingSpace]\[NonBreakingSpace]  ItemSize -> {Automatic,2},\[NonBreakingSpace]
	\[NonBreakingSpace]\[NonBreakingSpace]  Alignment -> Left,
	\[NonBreakingSpace]\[NonBreakingSpace]  BaseStyle -> {Bold}, 
	\[NonBreakingSpace]\[NonBreakingSpace]  Editable -> False]
\[NonBreakingSpace]\[NonBreakingSpace]  ]

(*Funzione che prende in input la lista dei simboli nullable e li stampa in una griglia*)
displayNullable[g0_] :=
	Module[{g = g0},
		Grid[g,
		Frame -> All, 
		Background->{White,White},
		ItemStyle->{Automatic},
		ItemSize->{{4,{4}}},
		BaseStyle->{Bold},
		Editable -> False]
	]

(*Funzione che prende in input la lista dei simboli First o dei simboli Follow e li stampa in una griglia*)
displayFirstFollow[g0_] :=
	Module[{g = g0},
		Grid[g,
			Frame -> All, 
			Background->{White,White},
			ItemStyle->{16,16},
			ItemSize->{{6,{Automatic}}},
			BaseStyle->{Bold},
			Editable -> False]
	]

(*Funzione che prende in input la grammatica e stampa la griglia.
Pu\[OGrave] prendere in input anche un cursore che evidenzia di blu la cella cliccata dall'utente*)
displayTable[g_,cursor_:0]:=
	Module[{backgrounds},
		backgrounds = checkErrors[g];
		Grid[g,
		Frame->If[MatchQ[xy[cursor],_Integer],All,{All,All,{xy[cursor]->{Thick,Blue}}}],
		Background->{White, White, backgrounds},
		ItemStyle->{Automatic},
		ItemSize->{{3,{4}}},
		BaseStyle->{Bold},
		Editable -> False]
	]

(*Funzione che prende in input la grammatica e la stampa con le produzioni nelle posizione corrette*)
displayTableSln[g0_]:=
	Module[{g = g0},
		Grid[g,
	        Frame -> All,
	        Background -> {White, White},
	        ItemStyle -> {Automatic},
	        ItemSize -> {{3, {4}}},
	        BaseStyle -> {Bold},
	        Editable -> False]
	]

(*Funzione che controlla la singola produzione inserita dall'utente. 
In caso essa non corrisponda a quella esatta della soluzione, viene colorata la cella di rosso.*)
checkErrors[g0_] :=
	Module[{g = g0},
	  tmp = List[];
	    Table[
			 (*Se indivua errore setto il colore alla cella a LightRed.
			   Se, invece, ha inserito la produzione corretta setto il coloro della cella a LightGreen *)
	            If[g[[xy[i][[1]], xy[i][[2]]]] != " " && g[[xy[i][[1]], xy[i][[2]]]] != "A" && g[[xy[i][[1]], xy[i][[2]]]] != "B" && g[[xy[i][[1]], xy[i][[2]]]] != "C" && g[[xy[i][[1]], xy[i][[2]]]] != "D",   
	              If[g[[xy[i][[1]], xy[i][[2]]]] != soluzione[[xy[i][[1]], xy[i][[2]]]],
	                  AppendTo[tmp, xy[i] -> LightRed],
	                  AppendTo[tmp, xy[i] -> LightGreen]];
	               ];
			,{i, cols + 1, rows * cols}];
	   tmp
   ]

(*Crea la tabella nullable vuota*)
\[NonBreakingSpace]createEmptyNullableCheckbox[sln_] := 
	Module[{copy = sln}, 
		Table[copy[[i, 2]] = Checkbox[], {i, 1, rows-1}];
		copy 
	]\[NonBreakingSpace]

(*Crea la tabella vuota con celle checkbox per i First e Follow*)
createEmptyFirstFollowCheckbox[sln_, tabFirst0_] :=\[NonBreakingSpace]
\[NonBreakingSpace]\[NonBreakingSpace]\[NonBreakingSpace] Module[{copy = sln, tabFirst = tabFirst0}, 
		Table[ If[i > 1 && j > 1, copy[[i, j]] = Checkbox[]], {i, rows}, {j, cols} ];
		If[tabFirst, copy[[1,cols]] = "\[Epsilon]";];
		copy 
	]

(*Crea la tabella finale delle produzioni vuota*)
createEmptyGrammar[sln_]:= 
	Module[{copy = sln},
		Table[ If[i > 1 && j > 1, copy[[i, j]] = " "], {i, rows}, {j, cols} ];
		copy
	]	

(*Funzione che prende in input le coordinate corrispondenti alla posizione del mouse 
e restituisce un intero settato sulla dimensione della griglia*)
loc[{x0_, y0_}] := 
	Module[{x = x0, y = y0},
		1 + Floor[cols x] + cols Floor[(1 - y) rows]
	]


(*Funzione che calcola l'esatta riga e colonna di ogni cella della tabella*)
row[n0_] := Module[{n = n0}, Quotient[n-1,cols]+1]
col[n0_] := Module[{n = n0}, Mod[n-1,cols]+1]

(*Funzione che presa in input una cella della griglia ne restituisce riga e colonna corrispondenti*)
xy[n0_] := Module[{n = n0}, {row[n],col[n]}]


(*Funzione che preso in input un seed genera la manipulate, possiamo chiamare questa funzione senza alcun parametro, in questo 
caso genera un esercizio random*)
GenerazioneInterfaccia[seed0_] :=
  Module[{seed = seed0},
    showNullableSln = False;
    
    (*Nuovo per espandere l'intero esercizio nullable*)
    showNullable = False;
    
    showFirst = False;
    showFollow = False;
    showSolution = False;
    num = seed;
    interface =
    
    (*Creazione di una Manipulate in cui l'espressione \[EGrave] una Grid contente l'intero esercizio *)
      Manipulate[
        Grid[
          {
            {Column[{Style["ANALISI SINTATTICA", Bold, FontSize -> 28
              ], " ", Style["ESERCIZIO DI GRAMMATICA N\[Degree]:" <> ToString[num], Bold, FontSize -> 20]}, Alignment -> Center]},
            {
              Column[
                {
                  " ",
                  Row[{Style["Generare gli insiemi Nullable, First e Follow per la seguente grammatica",
                     Bold, FontSize -> 15]}, Alignment -> Left],
                  " ",
                  Row[
                    {
                      Button[
                        "Nuovo Esercizio",
                        (
                        (*Al clic del bottone viene generata una nuova grammatica con seed random, settiamo il cursor a zero 
                        se assicurarci che nessuna sia selezionata  *)
                          cursor = 0;
                          Spacer[5];
                          (*? perch\[EGrave] prima di richiamare GenerazioneEsercizio creiamo una emptyGrammar?*)
                          emptyGrammar = createEmptyGrammar[soluzione];
                          GenerazioneEsercizio[];
                        ), ImageSize -> {Automatic},
                          BaseStyle -> {FontSize -> 15}
                      ],
                      " ",
                      " ",
                      DynamicModule[
                        {parametro = ""},
                        Row[
                          {
                          Style["oppure ripeti l'esercizio n\[Degree]:", Bold],
                             (*Input field in cui inserire un valore positivofra 1 e 10000 
                             per generare un eserciziocon uno specifico seed*)
                           InputField[
                                  Dynamic[
                                    parametro,
                                    If[NumberQ[#],
                                    (*Prendiamo il valore assoluto del numero per prevenire il caso in cui l'utente inserisca valori negativi*)
                                      parametro = Abs[#]]&
                                  ],
                                  Number,
                                  ImageSize -> {100,Automatic}
                            ], 
                            Spacer[4],
                            Button[
                              "Genera",
                              (*Controlliamo che il parametro sia compreso nel range 0-10000*)
                              If[parametro != "" && 0 <= parametro <= 10000,
                              (*Caso in cui l'utente abbia inserito un valore valido generiamo l' esercizio richiesto *)
                                cursor = 0;
                                emptyGrammar = createEmptyGrammar[soluzione];
                                (*Al clic del bottone viene generata una nuova grammatica con seed preso da tastiera*)
                                GenerazioneEsercizio[parametro];,
                                (*Messaggio di diagolo nel caso in cui l'utente non abbia inserito un valore valido *)
                                MessageDialog["Inserire un valore compreso fra 1 e 10000"
                                  ]
                              ],
                              ImageSize -> {Automatic},
                              BaseStyle -> {FontSize -> 15}
                            ]
                          }, Alignment->Center
                        ]
                      ]
                    }
                  ],
                  " ",
                  (*All'interno di una riga viene mostrata la grammatica. la funzione displatyGrammatic \[EGrave] una Grid*)
                  Row[{Column[{Style["GRAMMATICA", Bold, FontSize -> 
                    17], displayGrammatica[grammatica]}, Alignment -> Left]}],
                  " ",
                  (*Sezione che mostra i NULLABLE*)
                  
                  Column[
                    {
                    Style["NULLABLE", Bold, FontSize -> 17],
                    Framed["Un non terminale \[EGrave] nullable se pu\[OGrave] produrre una stringa vuota (\[Epsilon]). Seleziona i non terminali nullable.",
                    FrameStyle -> Directive[Thin, White], ImageSize -> {Automatic}, Alignment -> Top], 
                    
                   (*L'intero esercizio nullable \[EGrave] mostrato al click di prova esercizio*)
                   Button["Prova l'esercizio", 
                      showNullable = Not[showNullable],
                      ImageSize -> {Automatic},
                      BaseStyle -> {FontSize -> 15}], 
                   " ", 
                             
                   Dynamic[
                   If[showNullable,
                      Column[{
                      Row[
                        {
                          displayNullable[emptyNullableCheckbox],
                          "   ",
                          Dynamic[
                            If[showNullableSln,
                              Row[{Style["Soluzione Nullable", Bold], " ",
                                displayNullable[nullable]}, Alignment -> Center],
                              " "
                            ]
                          ] 
                        }
                      ],
                      (*Al clic del bottone viene mostrata la tabella con la soluzione per i simboli Nullable*)
                     Button["Mostra Soluzione Nullable", 
                     showNullableSln = Not[showNullableSln],
                     ImageSize -> {Automatic},
                     BaseStyle -> {FontSize -> 15}]}] 
                     ,
                   ""     
                    ]]
                    }
                  ],
                  " ",
                  
                  (*Sezione che mostra i FIRST*)
                  Column[
                    {
                    Style["FIRST", Bold, FontSize -> 17],
                          Framed["Dato un non terminale (ad esempio A,B), il suo insieme First \[EGrave] composto dai simboli terminali (compreso \[Epsilon])\nche possono apparire come carattere iniziale di una stringa derivata da una sua produzione.",
                          FrameStyle -> Directive[Thin, White], ImageSize -> {Automatic}, Alignment -> Top],
                    Row[
                        {
                          displayFirstFollow[emptyFirstCheckbox],
                          "   ",
                          Dynamic[
                            If[showFirst,
                              Column[{Style["Soluzione First", Bold],
                                 displayFirstFollow[first]}, Alignment -> Left],
                              " "]
                          ]                          
                        },
                        Alignment -> Left
                      ], " ",
                     (*Al clic del bottone viene mostrata la tabella con la soluzione per i simboli First*)
                      Button["Mostra Soluzione First", 
                      showFirst = Not[showFirst],
                      ImageSize -> {Automatic},
                      BaseStyle -> {FontSize -> 15}]
                    }
                  ],
                  " ",
                  (*Sezione che mostra i FOLLOW*)
                  Column[
                    {
                    Style["FOLLOW", Bold, FontSize -> 17],
                          Framed["Dato un non terminale, il suo insieme Follow \[EGrave] composto dai simboli terminali (e dal simbolo $)\nche possono apparire immediatamente dopo il non terminale in qualsiasi derivazione valida.",
                             FrameStyle -> Directive[Thin, White], ImageSize -> {Automatic}, Alignment -> Top],
                    Row[
                      {
                        displayFirstFollow[emptyFollowCheckbox],
                        "   ", 
                        Dynamic[
                            If[showFollow,
                              Column[{Style["Soluzione Follow", Bold],
                              displayFirstFollow[follow]}, Alignment -> Left],
                              ""
                            ]
                          ]
                        },
                        Alignment -> Left
                      ], " ",
                      (*Al clic del bottone viene mostrata la tabella con la soluzione per i simboli Follow*)
                      Button["Mostra Soluzione Follow", 
                      showFollow = Not[showFollow], 
                      ImageSize -> {Automatic},
                      BaseStyle -> {FontSize -> 15}]
                    }
                  ],
                  " ",
                  (*Sezione che mostra la TABELLA dell'esercizio*)
                  Row[
                    {
                      Column[
                        {
                          Style["TABELLA PRODUZIONI", Bold, FontSize -> 17],
                          Framed["Seleziona la cella in cui inserire la produzione e successivamente il bottone ad essa corrispondente.",
                             FrameStyle -> Directive[Thin, White], ImageSize -> {Automatic}, Alignment -> Top],
                          EventHandler[
                            Dynamic[displayTable[emptyGrammar, cursor
                              ]],
                     (*MouseClicked permette di calcolare tramite la funzione loc la posizione del mouse.
                       Controlla che l'utente non modifichi le intestazioni della tabella in cui sono presenti Terminali e Non terminali.
			           In caso contrario setta il cursore a -1.*)
                            "MouseClicked" :>
                              (
                                If[MemberQ[Range[1, rows * cols, cols
                                  ], loc[MousePosition["EventHandlerScaled"]]] || MemberQ[Range[1, cols
                                  ], loc[MousePosition["EventHandlerScaled"]]],
                                  cursor = -1,
                                  cursor = loc[MousePosition["EventHandlerScaled"
                                    ]]
                                ]
                              )
                          ],
                          Row[
						     (*Viene creata una serie di bottoni ciascuno indicante una delle produzioni della grammatica generata.
						     l'aggiunta di With[{i = i}] alll'interno di Table permette di salvare il valore di "i" all'interno dell'azione del
						     bottone. "i" va da 1 fino alla lunghezza di "listaProduzioi"*) 
						     Table[With[{i = i},
                                Button[
                                  listaProduzioni[[i]],
                                  If[cursor > 0,
                                    (*Grazie a With[{i = i}] possiamo accedere all'iesimo elemento in listaProduzione e andarlo a inserire all'interno 
                                    di emptyGrammar nella posizione cliccata dall'utente. 
                                    xy[cursor] restituisce la riga e colonna della cella "cursor" che \[EGrave] stata selezionata
                                    Attraverso xy[cursor][[1]] accediamo alla riga 
                                   Attraverso xy[cursor][[2]] accediamo alla colonna  *)
                               
                                  emptyGrammar[[xy[cursor][[1]], xy[ cursor][[2]]]] = listaProduzioni[[i]];
                                  
                                  (*Controllo che la produzione inserita nella cella sia nella posizione corretta. In caso contrario viene eseguito un Beep.*)
                                    If[emptyGrammar[[xy[cursor][[1]],xy[cursor][[2]]]] != soluzione[[xy[cursor][[1]], xy[cursor][[2]]]],
                                        Beep[]
                                    ]
                                  ], ImageSize -> {Automatic},
                                BaseStyle -> {FontSize -> 15}
                                ]
                              ],
                              (*"i" che va da 1 fino alla lunghezza di "listaProduzioi"*)
                              {i, 1, Length[listaProduzioni]}
                            ],
                            Spacer[0.4]
                          ],
                          Row[
                            {
                         (*Bottone che permette di svuotare il contenuto di una singola cella*)
                         Button["Svuota Cella",
                                If[cursor > 0,
                                (*xy[cursor] restituisce la riga e colonna della cella "cursor" che \[EGrave] stata selezionata
                                Attraverso xy[cursor][[1]] accediamo alla riga 
                                Attraverso xy[cursor][[2]] accediamo alla colonna  *)
                                  emptyGrammar[[xy[cursor][[1]], xy[cursor][[2]]]] = " "
                                ],ImageSize -> {Automatic},
                              BaseStyle -> {FontSize -> 15}],
                              " ",
                              (*Bottone che permette di svuotare il contenuto dell'intera griglia*)
                              Button["Svuota Tutto", Table[emptyGrammar
                                [[i, j]] = " ", {i, 2, rows}, {j, 2, cols}],ImageSize -> {Automatic},
                              BaseStyle -> {FontSize -> 15}],
                              " "
                            },
                            Alignment -> Center
                          ],
                          " ",
						 (*Al clic del bottone viene mostrata 
						   la tabella con la soluzione finale della tabella di Parsing*)
                          Button["Mostra Soluzione Tabella", showSolution
                             = Not[showSolution], ImageSize -> {Automatic},
                              BaseStyle -> {FontSize -> 15}],
                          " ",
                          Dynamic[
                            If[showSolution,
                              Column[{Style["Soluzione tabella delle produzioni",
                                 Bold], displayTableSln[soluzione]}, Alignment -> Left],
                              ""
                            ]
                          ]
                        }
                      ]
                    },
                    Alignment -> Center
                  ],
                  " "
                }
              ],
              " "
            }
          },
          Editable -> False
        ],
        (*"emptyNullableCheckbox" "emptyFirstCheckbox"  "emptyFollowCheckbox" "emptyGrammar" "cursor"
        sono i controlli della Manipulate per\[OGrave] in questo caso settando ControlType a None non viene effettuato 
        nessun conrollo *)
        {{emptyNullableCheckbox, createEmptyNullableCheckbox[nullable]}, ControlType -> None},
        {{emptyFirstCheckbox, createEmptyFirstFollowCheckbox[soluzione,True]}, ControlType -> None},
        {{emptyFollowCheckbox, createEmptyFirstFollowCheckbox[soluzione,False]}, ControlType -> None},
        {{emptyGrammar, createEmptyGrammar[soluzione]}, ControlType -> None},
        {{cursor, 0}, ControlType -> None},
        SaveDefinitions -> True,
        ContentSize -> {Automatic}
      ];
    interface
  ]


(*Funzione globale che permette di eseguire l'intero esercizio*)

GenerazioneEsercizio[seed0_:0] :=
	Module[{seed = seed0},
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
		
		(*Inizializzazione di tutte le parti della grammatica*)
		grammatica = GenerazioneGrammatica[];
		listaProduzioni = GenerazioneListaProduzioni[];
		nullable = GenerazioneNullable[];
		first = GenerazioneFirst[];
		follow = GenerazioneFollow[];
		soluzione = GenerazioneSoluzione[];
	
		(*Inizializzazione dell'interfaccia dell'esercizio*)
		rows = Length[soluzione[[All,1]]];
		cols = Length[soluzione[[1, All]]];
		interfaccia = GenerazioneInterfaccia[numEsercizio];,
		MessageDialog["Inserire un valore compreso fra 1 e 10000"]];
		
		interfaccia
	]




GenerazioneEsercizio[3]


Manipulate[
  Column[{
    "Testo del paragrafo",
    Dynamic@If[showParagraph, 
      CellPrint[TextCell["Nuovo paragrafo", "Text"]], 
      Nothing
    ],
    Button["Mostra/Nascondi paragrafo", showParagraph = !showParagraph]
  }],
  {{showParagraph, False}, ControlType -> None}
]





DynamicModule[{showParagraph = False},
  Column[{
    "Testo del paragrafo",
    Dynamic@If[showParagraph,
      TextCell["Ciao", "Text"],
      Nothing
    ],
    PopupMenu[
      Dynamic[showParagraph, (showParagraph = #) &],
      {False -> "Nascondi paragrafo", True -> "Mostra paragrafo"}
    ]
  }]
]




End[];


EndPackage[];
