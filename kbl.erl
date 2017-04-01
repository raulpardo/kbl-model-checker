-module(kbl).
-export([main/0]).

% Types are {proposition, --- "p"
%            connection,  --- c(agent1, agent2)
%            action,      --- a(agent1, agent2)
%            conjunction, --- \phi Λ \phi
%            negation,    --- ¬ \phi
%            knowledge}   --- K_agent1 \phi
-record(formula, {type, value, agent1, agent2, left, right}).

% TODO: More precise datatype
% -record(proposition, {value}).
% -record(conjunction, {}).
% -record(negation, {}).
% -record(knowledge, {agent, value}).
% -record(connection, {agent1, agent2}).
% -record(action, {agent1, agent2}).

% Social network models
-record(snm, {agents, connections, actions, environment, kbs, pps}).

% Connections
%-record(connection_name, {name, pairs}).

% Actions
%-record(actions, {name, pairs}).

% Actions
-record(kb, {agent, kb}).


main() ->
  % Create formula \phi = p \sedge q
  P = #formula{type=proposition, value=p},
  Q = #formula{type=proposition, value=q},
  PHI = #formula{type=conjunction, left=P, right=Q},

  % Create formula \psi = \neg K_alice p
  K = #formula{type=knowledge, agent1=alice, left=P},
  PSI = #formula{type=negation, left=K},

  % Create formula \gamma = c(alice,bob) \wedge a(charlie,alice)
  CON = #formula{type=connection, agent1=alice, agent2=bob},
  ACT = #formula{type=action, agent1=charlie, agent2=alice},
  GAMMA = #formula{type=conjunction, left=CON, right=ACT},

  % Create formula K_Charlie_Tauto = K_charlie \neg (\neg p \wedge p)
  NP = #formula{type=negation, left=P},
  C = #formula{type=conjunction, left=NP, right=P},
  N = #formula{type=negation, left=C},
  K_Charlie_Tauto = #formula{type=knowledge, agent1=charlie, left=N},

  % Creates an example social network model
  SNM = createSNM(),

  % Prints formula and checks whether it is satisfied in the SNM
  printfFormula(PHI),
  io:fwrite("~p~n", [satisfaction(SNM,PHI)]),
  printfFormula(PSI),
  io:fwrite("~p~n", [satisfaction(SNM,PSI)]),
  printfFormula(GAMMA),
  io:fwrite("~p~n", [satisfaction(SNM,GAMMA)]),
  printfFormula(K_Charlie_Tauto),
  io:fwrite("~p~n", [satisfaction(SNM,K_Charlie_Tauto)]),

  toString(PSI).


% Returns the following SNM:

%   alice                   bob           environment
% +-------+              +-------+        +-------+
% |       |      c       |       |        |       |
% |  p,q  +-------------^+   q   |        |   p   |
% |       |              |       |        |       |
% +---+---+              +----+--+        +-------+
%     ^                       |
%     |                       |
%     |       charlie         |c
%     |      +-------+        |
%     |      |       |        |
%     +------+       +^-------+
%     a      |       |
%            +-------+

createSNM() ->
  % Agents
  Agents = [alice,bob,charlie],

  % Pairs of a generic connection
  Connections = [{alice,bob}, {bob,charlie}],

  % Pair of a generic action
  Actions = [{charlie,alice}],

  % Environment's knowledge base
  Environment = [#formula{type=proposition, value=p}],

  % p
  P = #formula{type=proposition, value=p},
  % q
  Q = #formula{type=proposition, value=q},
  % K_alice p
  % K_Alice_P = #formula{type=knowledge, agent1=alice, left=P},

  % Agents knowledge bases
  Alice_KB = #kb{agent=alice, kb=[P,Q]},
  Bob_KB = #kb{agent=bob, kb=[Q]},
  Charlie_KB = #kb{agent=charlie, kb=[]},

  % Putting everything together
  #snm{agents=Agents,
       connections=Connections,
       actions=Actions,
       environment=Environment,
       kbs=[Alice_KB, Bob_KB, Charlie_KB],
       pps=[]}.

% Implementation of the satisfaction relation |=
satisfaction(SNM, Formula) ->
  case Formula#formula.type of
    proposition -> lists:member(Formula, SNM#snm.environment);

    connection  -> lists:member({Formula#formula.agent1, Formula#formula.agent2}, SNM#snm.connections);

    action      -> lists:member({Formula#formula.agent1, Formula#formula.agent2}, SNM#snm.actions);

    negation    -> not satisfaction(SNM,Formula#formula.left);

    conjunction -> satisfaction(SNM, Formula#formula.left) and satisfaction(SNM, Formula#formula.right);

    knowledge   -> Agent_KB = find_kb(Formula#formula.agent1, SNM#snm.kbs),
                   check_kb(Formula#formula.left, Agent_KB#kb.kb)
  end.


% Check whether Formula is derivable from KB using MOLTAP
check_kb(Formula, KB) ->
  case length(KB) of
    0 -> call_moltap(toString(Formula)); % In case Formula is a tautology
    _ -> KB_Conj = create_conjunction(KB,[]),
         ToCheck = KB_Conj ++ " -> " ++ toString(Formula),
         call_moltap(ToCheck)
  end.

% We call the modal theorem prover moltap
call_moltap(ToCheck) ->
  Command = "/home/pardo/moltap/moltap -f '" ++ ToCheck ++"'", % TODO: Add variable with moltap directory.
                                                               % TODO: Check whether moltap is installed.
  io:fwrite("To check by moltap: ~s~n",[ToCheck]),
  case os:cmd(Command) of
    "true\n" -> true;
    "false\n" -> false
  end.

% Auxiliary function to create the conjunction of the KB of an agent
% We're assuming that the length of [H|T] is greater than 0
create_conjunction([H|T],Acc) ->
  case length([H|T]) of
    1 -> Acc ++ "(" ++ toString(H) ++ ")";
    _ -> NewAcc = Acc ++ "(" ++ toString(H) ++ " and ",
         create_conjunction(T,NewAcc) ++ ")"
  end.

find_kb(_Agent, []) ->
  false;

find_kb(Agent, [KB | T]) ->
  case KB#kb.agent of
    Agent -> KB;
    _     -> find_kb(Agent, T)
  end.

% Add a break line after printing
printfFormula(Formula) ->
  io:fwrite("~s~n", [toString(Formula)]).

% Converts Formula into a string
toString(Formula) ->
  case Formula#formula.type of
    proposition -> atom_to_list(Formula#formula.value);

    connection  -> "c_"++atom_to_list(Formula#formula.agent1) ++ "_" ++ atom_to_list(Formula#formula.agent2);

    action      -> "a_"++atom_to_list(Formula#formula.agent1) ++ "_" ++ atom_to_list(Formula#formula.agent2);

    negation    -> "not (" ++ toString(Formula#formula.left) ++ ")";

    knowledge   -> "K_" ++ atom_to_list(Formula#formula.agent1) ++ " (" ++ toString(Formula#formula.left) ++ ")";

    conjunction -> "(" ++ toString(Formula#formula.left) ++
                   " and " ++
                   toString(Formula#formula.right) ++ ")"
  end.

% Recursively print all the elements of the formula. === NOT USED FOR NOW
% printFormula(Formula) ->
%     case Formula#formula.type of
%       proposition -> io:fwrite("~p", [atom_to_list(Formula#formula.value)]);
%
%       connection  -> io:fwrite("c(~p,~p)", [atom_to_list(Formula#formula.agent1), atom_to_list(Formula#formula.agent2)]);
%
%       action      -> io:fwrite("a(~p,~p)", [atom_to_list(Formula#formula.agent1), atom_to_list(Formula#formula.agent2)]);
%
%       negation    -> io:fwrite("¬"),
%                      printFormula(Formula#formula.left);
%
%       knowledge   -> io:fwrite("K_~p",[atom_to_list(Formula#formula.agent1)]),
%                      printFormula(Formula#formula.left);
%
%       conjunction -> printFormula(Formula#formula.left),
%                      io:fwrite(" Λ "),
%                      printFormula(Formula#formula.right)
%     end.
