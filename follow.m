(* ::Package:: *)

tuttiNonTerminali = CharacterRange["A","D"];
numNonTerminali = Length[tuttiNonTerminali];
tuttiTerminali = CharacterRange["a", "z"];
grammatica = {{"A", {"bBC", "a"}}, {"B", {"d", "c"}}, {"C", {"gf", "De", "\[Epsilon]"}}, {"D", {"i", "h"}}};
nullable = {{"A", False}, {"B", False}, {"C", True}, {"D", False}};
first = {{"A", {"a", "b"}}, {"B", {"c", "d"}}, {"C", {"g", "h", "i", "\[Epsilon]"}}, {"D", {"h", "i"}}};
(************************************************************************************************************************************************)

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
					(*Se il prossimo elemento \[EGrave] un Terminale*)
					MemberQ[tuttiTerminali, StringTake[produzioneCorrente, {k + 1}]],
						Table[
							(*Cerco il Non Terminale corrente nei Follow e aggiungo alla sua lista il carattere Terminale*)
							If[nonTerminaleDaControllare == follow[[l, 1]],
								AppendTo[follow[[l, 2]], StringTake[produzioneCorrente, {k + 1}]];
							];
						,{l, 1, Length[follow]}
						];
					,
					(*Se il prossimo elemento \[EGrave] un Non Terminale*)
					MemberQ[tuttiNonTerminali, StringTake[produzioneCorrente, {k + 1}]],
						firstProssimoNonTerminale = List[];
						Table[
							(*Cerca il First del Non Terminale successivo*)
							If[StringTake[produzioneCorrente, {k + 1}] == first[[l, 1]],
								firstProssimoNonTerminale = first[[l, 2]];
								(*Se il First contiene \[Epsilon] lo rimuove*)
								If[MemberQ[firstProssimoNonTerminale, "\[Epsilon]"],
									firstProssimoNonTerminale = Drop[firstProssimoNonTerminale, Flatten[Position[firstProssimoNonTerminale, "\[Epsilon]"]]];
								];
							];
						,{l, 1, Length[first]}
						];
						
						Table[
							(*Cerco il Non Terminale corrente nei Follow e aggiungo alla sua lista il First del Non Terminale successivo*)
							If[nonTerminaleDaControllare == follow[[l, 1]],
								AppendTo[follow[[l, 2]], firstProssimoNonTerminale];
							];
						,{l, 1, Length[follow]}
						];
						
						(*Se il Non Terminale successivo \[EGrave] Nullable bisogner\[AGrave] aggiungere il suo Follow a quello del Non Terminale corrente*)
						Table[
							If[StringTake[produzioneCorrente, {k + 1}] == nullable[[l, 1]],
								PrependTo[listaRicontrollo2, {nonTerminaleDaControllare, StringTake[produzioneCorrente, {k + 1}]}];
							];
						,{l, 1, Length[nullable]}
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
	continua = True;
	index1 = 0;
	While[continua && index1 <= Length[follow],
		index1++;
		If[listaRicontrollo1[[i, 1]] == follow[[index1, 1]], continua = False];	
	];
	continua = True;
	index2 = 0;
	While[continua && index2 <= Length[follow],
		index2++;
		If[listaRicontrollo1[[i, 2]] == follow[[index2, 1]], continua = False];	
	];
	AppendTo[follow[[index1, 2]], follow[[index2, 2]]];
,{i, 1, Length[listaRicontrollo1]}
];

(*Ad ogni Non Terminale che precede un Non Terminale Nullable viene aggiunto il Follow del Non Terminale Nullable*)
Table[
	continua = True;
	index1 = 0;
	While[continua && index1 <= Length[follow],
		index1++;
		If[listaRicontrollo2[[i, 1]] == follow[[index1, 1]], continua = False];	
	];
	continua = True;
	index2 = 0;
	While[continua && index2 <= Length[follow],
		index2++;
		If[listaRicontrollo2[[i, 2]] == follow[[index2, 1]], continua = False];	
	];
	AppendTo[follow[[index1, 2]], follow[[index2, 2]]];
,{i, 1, Length[listaRicontrollo2]}
];

Table[
	follow[[i, 2]] = Flatten[follow[[i, 2]]];
	DeleteDuplicates[follow[[i, 2]]];
	Sort[follow[[i, 2]]];
,{i, 1, Length[follow]}	
];

follow

