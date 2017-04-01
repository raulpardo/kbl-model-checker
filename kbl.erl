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
%-record(connections, {name, pairs}).

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

  % Creates an example social network model
  SNM = createSNM(),

  % Prints formula and checks whether it is satisfied in the SNM
  printfFormula(PHI),
  io:fwrite("~p~n", [satisfaction(SNM,PHI)]),
  printfFormula(PSI),
  io:fwrite("~p~n", [satisfaction(SNM,PSI)]),
  printfFormula(GAMMA),
  io:fwrite("~p~n", [satisfaction(SNM,GAMMA)]).


% Returns the following SNM:

%   alice                   bob           environment
% +-------+              +-------+        +-------+
% |       |      c       |       |        |       |
% |   p   +-------------^+   q   |        |   p   |
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
  Agents = [alice,bob,charlie],
  Connections = [{alice,bob}, {bob,charlie}],
  Actions = [{charlie,alice}],
  Environment = [#formula{type=proposition, value=p}],
  Alice_KB = #kb{agent=alice, kb=[#formula{type=proposition, value=p}]},
  Bob_KB = #kb{agent=bob, kb=[#formula{type=proposition, value=q}]},
  Charlie_KB = #kb{agent=charlie, kb=[]},
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
                   lists:member(Formula#formula.left, Agent_KB#kb.kb)
  end.

find_kb(_Agent, []) ->
  false;

find_kb(Agent, [KB | T]) ->
  case KB#kb.agent of
    Agent -> KB;
    _     -> find_kb(Agent, T)
  end.

% Recursively print all the elements of the formula.
printFormula(Formula) ->
    case Formula#formula.type of
      proposition -> io:fwrite("~p", [atom_to_list(Formula#formula.value)]);

      connection  -> io:fwrite("c(~p,~p)", [atom_to_list(Formula#formula.agent1), atom_to_list(Formula#formula.agent2)]);

      action      -> io:fwrite("a(~p,~p)", [atom_to_list(Formula#formula.agent1), atom_to_list(Formula#formula.agent2)]);

      negation    -> io:fwrite("¬"),
                     printFormula(Formula#formula.left);

      knowledge   -> io:fwrite("K_~p",[atom_to_list(Formula#formula.agent1)]),
                     printFormula(Formula#formula.left);

      conjunction -> printFormula(Formula#formula.left),
                     io:fwrite(" Λ "),
                     printFormula(Formula#formula.right)
    end.

% Add a break line after printing
printfFormula(Formula) ->
  printFormula(Formula),
  io:fwrite("~n").
