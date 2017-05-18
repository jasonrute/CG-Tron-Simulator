import sys, getopt
import math
import random 
import heapq  
import time  
import collections
from subprocess import Popen, PIPE, STDOUT
from threading  import Thread
from queue import Queue, Empty
import io
import itertools


###################
# System Settings #
###################

# Set seed for randomness
random.seed(1)


#############
# Constants #
#############

# Game constants
TIME_LIMIT_PREPROCESSING = 1.23 #sec
TIME_LIMIT_FIRST_ROUND = 1.00 #sec
TIME_LIMIT_LAP = 0.10 #sec
HEIGHT = 20
WIDTH = 30
NUMBER_OF_PLAYERS = 4 # Sometimes they are dead or absent

# My constants
BUFFER = 0.01
DIRECTIONS = {(0,1):"DOWN",(1,0):"RIGHT",(0,-1):"UP",(-1,0):"LEFT"}
MOVES = {"DOWN":(0,1),"RIGHT":(1,0),"UP":(0,-1),"LEFT":(-1,0)}
CCW_ROTATION = {(0,1):(1,0), (1,0):(0,-1), (0,-1):(-1,0), (-1,0):(0,1)}
CW_ROTATION = {(0,1):(-1,0), (-1,0):(0,-1), (0,-1):(1,0), (1,0):(0,1)}


############
# Warnings #
############

WARNINGS = {"OUT OF TIME", "OUT_OF_TIME:", "Warning:"}

##################
# Debugging code #
##################

# Channels turned on (True) and off (False)
DEBUG_CHANNELS = {
    "lap": True, # Time that the previous move took
    "time_data": False, # Times for various parts of the code
    "score": True, # Scores for various parts of the minimax algorithm
    "out_of_time": True,
    None: True  # Default channel
    }

def debug(*args, **kwargs):
    if "channel" in kwargs:
        channel = kwargs["channel"]
        del kwargs["channel"]
    else:
        channel = None
    
    if channel in DEBUG_CHANNELS and DEBUG_CHANNELS[channel]:
        print(*args, **kwargs, file=sys.stderr, flush=True)


############################
# 2D list helper functions #
############################

def copy_2D_list(two_dim_list):
    return [l.copy() for l in two_dim_list]

EMPTY_GRID = [[None] * HEIGHT for _ in range(WIDTH)]

# Neighbors
NBRS = copy_2D_list(EMPTY_GRID)
# Corners
NBRS[0][0] = frozenset([(0,1),(1,0)])
NBRS[0][HEIGHT-1] = frozenset([(0,HEIGHT-2),(1,HEIGHT-1)])
NBRS[WIDTH-1][0] = frozenset([(WIDTH-1,1),(WIDTH-2,0)])
NBRS[WIDTH-1][HEIGHT-1] = frozenset([(WIDTH-1,HEIGHT-2),(WIDTH-2,HEIGHT-1)])
# First and last rows
for x in range(1,WIDTH-1):
    NBRS[x][0] = frozenset([(x-1,0),(x+1,0),(x,1)])
    NBRS[x][HEIGHT-1] = frozenset([(x-1,HEIGHT-1),(x+1,HEIGHT-1),(x,HEIGHT-2)])
# First and last columns
for y in range(1,HEIGHT-1):
    NBRS[0][y] = frozenset([(0,y-1),(0,y+1),(1,y)])
    NBRS[WIDTH-1][y] = frozenset([(WIDTH-1,y-1),(WIDTH-1,y+1),(WIDTH-2,y)])
# The inner cells
for x in range(1,WIDTH-1):
    for y in range(1,HEIGHT-1):
        NBRS[x][y] = frozenset([(x,y-1),(x,y+1),(x-1,y),(x+1,y)])
##############
# Tron class #
##############

class Tron():
    """
    A Tron board with all the players on it.
    """

    def __init__(self, grid, heads, nbrs, comp_boundaries, comp_list):
        """
        On initial creation:
        grid = [[None for y in range(HEIGHT)] for x in range(WIDTH)]
        heads = [None] * NUMBER_OF_PLAYERS
        nbrs = ...
        """
        self.grid = grid
        self.heads = heads
        self.nbrs = nbrs
        self.comp_boundaries = comp_boundaries
        self.comp_list = comp_list

    def copy(self):
        new_grid = copy_2D_list(self.grid)
        new_heads = self.heads.copy()
        new_nbrs = copy_2D_list(self.nbrs)
        new_comp_boundaries = copy_2D_list(self.comp_boundaries)
        new_comp_list = self.comp_list.copy()
        return Tron(new_grid, new_heads, new_nbrs, new_comp_boundaries, new_comp_list)

    def debug_grid(self):
        for y in range(20):
            row = []
            for x in range(30):
                if self.grid[x][y]:
                    _, prev_node, next_node = self.grid[x][y]
                else:
                    prev_node, next_node = None, None
                
                if prev_node:
                    x1, y1 = prev_node
                    dp = (x1-x,y1-y)
                else:
                    dp = None
                
                if next_node:
                    x1, y1 = next_node
                    dn = (x1-x,y1-y)
                else:
                    dn = None

                row.append({frozenset({(0,1),(1,0)}):  "┏━",
                            frozenset({(0,1),(0,-1)}): "┃ ",
                            frozenset({(0,1),(-1,0)}): "┓ ",
                            frozenset({(0,1),None}):   "╻ ",
                            frozenset({(1,0),(0,-1)}): "┗━",
                            frozenset({(1,0),(-1,0)}): "━━",
                            frozenset({(1,0),None}):   "╺━",
                            frozenset({(0,-1),(-1,0)}):"┛ ",
                            frozenset({(0,-1),None}):  "╹ ",
                            frozenset({(-1,0),None}):  "╸ ",
                            frozenset({None}):         ". "}[frozenset({dp,dn})])
            
            print("".join(row))
    
    def debug_nbrs(self):
        for y in range(20):
            print(" ".join(str(len(self.nbrs[x][y])) for x in range(30)))

    def update_head(self, player, head_x, head_y):
        """
        Called every time I want to move the head.
        """
        if self.heads[player] == (head_x, head_y):
            # Head is same.  Don't do anything
            return

        if not self.heads[player]:
            # First head
            self.grid[head_x][head_y] = (player, None, None)
        else:
            # Move head from previous position
            prev_head_x, prev_head_y = self.heads[player]

            # Point to previous head
            self.grid[head_x][head_y] = (player, (prev_head_x, prev_head_y), None)
            self.grid[prev_head_x][prev_head_y] \
                = (player, self.grid[prev_head_x][prev_head_y][1], (head_x, head_y))
        
            # Remove nbrs from the previous head
            prev_head_x, prev_head_y = self.heads[player]
            for x, y in self.nbrs[prev_head_x][prev_head_y]:
                self.nbrs[x][y] = self.nbrs[x][y] - {(prev_head_x, prev_head_y)}
            self.nbrs[prev_head_x][prev_head_y] = frozenset()
        
        # Update head pointer
        self.heads[player] = (head_x, head_y)

    def kill_player(self, player):
        """
        Remove player from the game.
        """
        if not self.heads[player]:
            # Already removed
            return
        
        # Follow path, remove player from self.grid, and fix self.nbrs
        all_nbrs = NBRS
        prev_node = self.heads[player] # Next node to remove

        while prev_node:
            x0, y0 = prev_node
            for x,y in all_nbrs[x0][y0]:
                if self.grid[x][y] == None or (x, y) in self.heads:
                    self.nbrs[x0][y0] = self.nbrs[x0][y0] | {(x,y)}
                    self.nbrs[x][y] = self.nbrs[x][y] | {(x0,y0)}

            _, prev_node, next_node = self.grid[x0][y0]
            self.grid[x0][y0] = None
        
        # Mark player as dead
        self.heads[player] = None

    def valid_moves(self, player):
        hx, hy = self.heads[player]
        for x, y in sorted(self.nbrs[hx][hy]):
            if not self.grid[x][y]:
                yield x,y

##################
# Player process #
##################

"""
Use this technique to avoid blocking of my streams:
http://stackoverflow.com/a/4896288/3494621
"""

# Helper functions

def _enqueue_output(out, queue):
    """
    Wrap the output stream in a queue, which when placed in a thread, 
    will to avoid blocking.
    """
    for line in iter(out.readline, ""): # loop over the out file
        queue.put(line)
    out.close()

def _convert_output_stream_to_threaded_queue(out):
    out_queue = Queue()
    t = Thread(target=_enqueue_output, args=(out, out_queue))
    t.daemon = True # thread dies with the program
    t.start()
    return out_queue

def _read_non_blocking(queue, timeout):
    """
    Enumerate all the lines currently in the stream queue without waiting for 
    more to be added later.  The timeout is how long I wait for something to
    come through the buffer.  Once it does, I read without waiting.
    """
    while True:
        # read line without blocking
        try: 
            yield queue.get(timeout=timeout) # or queue.get_nowait()
            timeout = 0
        except Empty:
            return # done enumerating

class Player_Process():
    """
    Keeps track of a players process including all the tricks we use to avoid
    issues with the streams blocking.
    """

    def __init__(self, program_name, options=[]):
        p = Popen(['python3', '-u', program_name] + options, # -u prevents 
                                                             # buffering on 
                                                             # the child's side
                  stdout=PIPE, stdin=PIPE, stderr=PIPE, 
                  bufsize=1, # Prevents buffering parent's end
                  universal_newlines=True) # Streams are text instead of bytes
        self._process = p
        self._stdout_queue = _convert_output_stream_to_threaded_queue(p.stdout)
        self._stderr_queue = _convert_output_stream_to_threaded_queue(p.stderr)
        self.stdin = p.stdin

    def read_stdout(self, timeout = .1):
        return _read_non_blocking(self._stdout_queue, timeout=timeout)

    def read_stderr(self, timeout = .1):
        return _read_non_blocking(self._stderr_queue, timeout=timeout)

    def kill(self):
        self._process.kill()

##############
# Game class #
##############

class Game():
    """
    Stores the current state of the game.
    """
    
    def __init__(self, id_number, config_str, player_program_list, time_limits, verbose, show_map):
        """
        Initializes all game data
        """

        #
        # Counters/Timers
        #
        self.turn = -1 # Counter will update at beginning of round.
        self.start_time = time.perf_counter()
        self.total_time = time.perf_counter()

        #
        # Fixed information
        #

        self.id_number = id_number
        self.number_of_starting_players = len(player_program_list)
        self.player_program_list = player_program_list
        max_name_len = max([len(name) for name in player_program_list])
        self.padded_names = [name.ljust(max_name_len) for name in player_program_list]
        self.config_str = config_str
        self.time_limits = time_limits
        self.verbose = verbose
        self.show_map = show_map

        # Starting positions:
        self.starting_positions = []
        config_str = config_str.replace(")(", " ").replace("(", "").replace(")", "")
        pairs = config_str.split()
        if len(pairs) != self.number_of_starting_players:
            raise Exception("Starting configuration doesn't match number of players")
        for pair in config_str.split():
            x, y = [int(i) for i in pair.split(",")]
            self.starting_positions.append((x,y))

        #
        # Start the programs running as subprocesses
        #
        self.player_processes = []
        for program_name in player_program_list:
            options = []
            if not self.time_limits:
                options = ['--no-time-limit']
            self.player_processes.append(Player_Process(program_name, options))

        #
        # Some important 2d arrays
        #
        
        # Empty grid
        empty_grid = [[None] * HEIGHT for _ in range(WIDTH)]
        self.empty_grid = empty_grid

        # Neighbors
        nbrs = copy_2D_list(empty_grid)
        # Corners
        nbrs[0][0] = frozenset([(0,1),(1,0)])
        nbrs[0][HEIGHT-1] = frozenset([(0,HEIGHT-2),(1,HEIGHT-1)])
        nbrs[WIDTH-1][0] = frozenset([(WIDTH-1,1),(WIDTH-2,0)])
        nbrs[WIDTH-1][HEIGHT-1] = frozenset([(WIDTH-1,HEIGHT-2),(WIDTH-2,HEIGHT-1)])
        # First and last rows
        for x in range(1,WIDTH-1):
            nbrs[x][0] = frozenset([(x-1,0),(x+1,0),(x,1)])
            nbrs[x][HEIGHT-1] = frozenset([(x-1,HEIGHT-1),(x+1,HEIGHT-1),(x,HEIGHT-2)])
        # First and last columns
        for y in range(1,HEIGHT-1):
            nbrs[0][y] = frozenset([(0,y-1),(0,y+1),(1,y)])
            nbrs[WIDTH-1][y] = frozenset([(WIDTH-1,y-1),(WIDTH-1,y+1),(WIDTH-2,y)])
        # The inner cells
        for x in range(1,WIDTH-1):
            for y in range(1,HEIGHT-1):
                nbrs[x][y] = frozenset([(x,y-1),(x,y+1),(x-1,y),(x+1,y)])
        """
        def neighbors(x,y):
            if x > 0:
                yield x-1, y
            if x < WIDTH - 1:
                yield x+1, y
            if y > 0:
                yield x, y-1
            if y < HEIGHT - 1:
                yield x, y+1
                
        nbrs = [[frozenset(neighbors(x,y)) for y in range(HEIGHT)] for x in range(WIDTH)]    
        """
        self.nbrs = nbrs

        # Component boundary for one big component
        starting_comp_boundaries = copy_2D_list(empty_grid)
        to_visit = collections.deque()
        to_visit.append((0,0))
        while to_visit:
            x, y = to_visit.popleft()
            # find outside wall:
            dx, dy = (1,0)
            while (x+dx, y+dy) in nbrs[x][y]:
                dx, dy = CCW_ROTATION[dx, dy]
            # Rotate CW until find a neighbor
            ldx, ldy = dx, dy
            while (x+ldx, y+ldy) not in nbrs[x][y]: 
                ldx, ldy = CW_ROTATION[ldx, ldy]
            left_x, left_y = x+ldx, y+ldy
            # Rotate CCW until find a neighbor
            rdx, rdy = dx, dy
            while (x+rdx, y+rdy) not in nbrs[x][y]:
                rdx, rdy = CCW_ROTATION[rdx, rdy]
            right_x, right_y = x+rdx, y+rdy
            starting_comp_boundaries[x][y] = ((0, (left_x, left_y), (right_x, right_y)),) 
            if not starting_comp_boundaries[left_x][left_y]:
                to_visit.append((left_x, left_y))
            if not starting_comp_boundaries[right_x][right_y]:
                to_visit.append((right_x, right_y))
        
        #
        # Information which changes each turn
        #
        
        # This is the main Tron class which is updated every round.
        tron_grid = copy_2D_list(empty_grid)
        tron_heads = [None] * NUMBER_OF_PLAYERS
        tron_nbrs = copy_2D_list(nbrs)
        tron_comp_boundaries = copy_2D_list(empty_grid)
        tron_comp_list = [(0, WIDTH * HEIGHT, ())]
        
        self.tron = Tron(tron_grid, tron_heads, tron_nbrs, tron_comp_boundaries, tron_comp_list)
        
        # Add initial head for all players
        for i in range(self.number_of_starting_players):
            x, y = self.starting_positions[i]
            self.tron.update_head(i, x, y)

        self.current_player = 0
        self.loss_order = [] # list of players as they lose
        self.issue_logs = [None for p in player_program_list]
        self.warnings = [[] for p in player_program_list]
        self.sum_times = [0 for p in player_program_list]
        self.max_times = [0 for p in player_program_list]
        self.player_turns = [0 for p in player_program_list]

    def kill_player(self, player):
        # Remove from tron board
        self.tron.kill_player(player)

        # Close the process and remove from process list
        self.player_processes[player].kill()
        self.player_processes[player] = None

        # Mark player as lost
        self.loss_order.append(player)

    def pregame(self):
        print("==========================")
        print("Game:", self.id_number)
        print("Configuration:", self.config_str)
        print("Players:")
        for player, player_name in enumerate(self.player_program_list):
            print(player, ":", player_name)


    def is_active(self):
        return len([p for p in self.player_processes if p]) > 1 # Two or more players left

    def send_inputs_to_player(self):
        try:
            current_player_stdin = self.player_processes[self.current_player].stdin

            # n: total number of players (2 to 4).
            # p: your player number (0 to 3).
            n = self.number_of_starting_players
            p = self.current_player
            print(n, p, file=current_player_stdin)
            
            for i in range(self.number_of_starting_players):
                # x0: starting X coordinate of lightcycle (or -1)
                # y0: starting Y coordinate of lightcycle (or -1)
                # x1: starting X coordinate of lightcycle (can be the same as X0 if you play before this player)
                # y1: starting Y coordinate of lightcycle (can be the same as Y0 if you play before this player)
                if self.player_processes[i]:
                    x0, y0 = self.starting_positions[i]
                    x1, y1 = self.tron.heads[i]
                else:
                    x0, y0, x1, y1 = -1, -1, -1, -1
                print(x0, y0, x1, y1, file=current_player_stdin)

            return time.perf_counter(), False # no errors

        except BrokenPipeError:
            print("Broken Pipe Error")
            return time.perf_counter(), True # errors (Program likely crashed)

    def read_player_streams(self, timeout = 0.1):
        p = self.player_processes[self.current_player]

        # read from stdout first since that means they are done with their turn
        stdout_stream = list(p.read_stdout(timeout = timeout))
        output_time = time.perf_counter()
        # read stderr next with no timeout since it should all be put into 
        # the stream by now
        stderr_stream = list(p.read_stderr(timeout = 0.01))

        return output_time, stdout_stream, stderr_stream

    def process_players_output(self, stdout_stream):
        issue_flag = False # used to flag undesired behavior
        message = ""
        if not stdout_stream:
            self.kill_player(self.current_player)
            message += "did not provide any output. (CRASHED?)"
            issue_flag = True

        elif len(stdout_stream) == 1:
            move = stdout_stream[0].rstrip()
            # current head
            x0, y0 = self.tron.heads[self.current_player]
            if move in MOVES:
                # the move
                move = stdout_stream[0].rstrip()
                # find new head
                dx, dy = MOVES[move]
                x1, y1 = x0+dx, y0+dy

                # check if a valid move.
                valid_moves = list(self.tron.valid_moves(self.current_player))
                if (x1,y1) in valid_moves:
                    self.tron.update_head(self.current_player, x1, y1)
                    message += "moves " + move + "."
                elif self.tron.nbrs:
                    self.kill_player(self.current_player)
                    message += "makes an invalid move." 
                    
                    if valid_moves:
                        message += " (VALID MOVES EXISTED!)"
                        issue_flag = True
                    else:
                        message += " (No valid moves existed.)"
            else:
                valid_moves = list(self.tron.valid_moves(self.current_player))
                self.kill_player(self.current_player)
                message += "plays unrecognized move '" + move + "'."
                
                if valid_moves:
                    message += " (VALID MOVES EXISTED!)"
                    issue_flag = True
                else:
                    message += " (No valid moves existed.)"
        else:
            self.kill_player(self.current_player)
            message += "has too many outputs."
            issue_flag = True

        return message, issue_flag

    def process_players_errors(self, stderr_stream):
        warning_set = set() # A set to avoid duplicates
        for line in stderr_stream:
            line = line.rstrip()
            if line in WARNINGS or line.split()[0] in WARNINGS:
                warning_set.add((self.turn, line))
        self.warnings[self.current_player].extend(warning_set)

    def record_times(self, input_time, output_time):
        player = self.current_player
        if self.player_turns[player]: # skip first turn
            turn_time = output_time - input_time
            self.sum_times[player] += turn_time
            if self.max_times[player] < turn_time:
                self.max_times[player] = turn_time

        self.player_turns[player] += 1

    def print_turn_data(self, stdout_stream, stderr_stream, message, issue_flag, input_time, output_time):
        player_name = self.player_program_list[self.current_player]
        print("--------------------------")
        print("Turn", self.turn, "(Player {})".format(self.current_player), player_name)
        
        print("Standard Error Stream:")
        for line in stderr_stream:
            print(">", line, end="")
        print("Standard Output Stream:")
        for line in stdout_stream:
            print(">", line, end="")
        print("Game Information:")
        print(">", player_name, message)
        print("Turn time:", output_time - input_time, "sec")
        if self.show_map: self.tron.debug_grid()

    def print_error_report(self, player):
        turn, stdout_stream, stderr_stream, \
              message, input_flag, output_flag = self.issue_logs[player]
        player_name = self.player_program_list[player]
        print("    Error on turn", self.turn)
        
        print("    Standard Error Stream:")
        for line in stderr_stream:
            print("    >", line, end="")
        print("    Standard Output Stream:")
        for line in stdout_stream:
            print("    >", line, end="")
        print("    Game Information:")
        print("    >", player_name, message)
        #self.tron.debug_grid()


    def increment_current_player(self): # takes into account dead players
        self.current_player = (self.current_player + 1) \
                                % self.number_of_starting_players

        while not self.player_processes[self.current_player]: # That player is dead
            self.current_player = (self.current_player + 1) \
                                % self.number_of_starting_players

    def one_turn(self):
        """
        Perform one turn in the game from sending input to reading the streams
        """

        #
        # Mark time that the previous move took
        #
        #if self.turn >= 0:
        #    debug("prev turn time:", time.perf_counter() - self.start_time, channel="lap")        
        
        self.start_time = time.perf_counter()
        self.turn += 1

        #
        # Read inputs and update game variables
        #
            
        input_time, input_flag = self.send_inputs_to_player()
        output_time, stdout_stream, stderr_stream = self.read_player_streams(timeout = 2)
        message, output_flag = self.process_players_output(stdout_stream)
        warnings = self.process_players_errors(stderr_stream)
        self.record_times(input_time, output_time)
        if input_flag or output_flag:
            self.issue_logs[self.current_player] = (self.turn, stdout_stream, 
                                                     stderr_stream, message, 
                                                     input_flag, output_flag)
        if self.verbose:
            self.print_turn_data(stdout_stream, stderr_stream, message, output_flag, input_time, output_time)
        self.increment_current_player() # takes into account dead players

    def end_of_game(self):
        # Kill remaining player
        for i in range(self.number_of_starting_players):
            if self.player_processes[i]:
                self.kill_player(i)

        print("--------------------------")
        print("Game", self.id_number, "results:")
        for place, player in enumerate(reversed(self.loss_order)):
            if self.player_turns[player]:
                ave_time = self.sum_times[player]/self.player_turns[player]
            else:
                ave_time = 0.0
            max_time = self.max_times[player]
            print(place + 1, ":", 
                "(Player {})".format(player),
                self.padded_names[player],
                "   [ave: {:.5f} sec, max: {:.5f} sec]".format(ave_time, max_time))
            if self.issue_logs[player]:
                self.print_error_report(player)
            if self.warnings[player]:
                for turn, message in self.warnings[player]:
                    print("    Warning on turn", turn, ":", message)


        print("Total time:", time.perf_counter() - self.total_time, "sec")

####################
# Tournament class #
####################

class Tournament():
    def __init__(self, number_of_games, program_names, game_arity, time_limits, verbose, show_map):
        self.number_of_games = number_of_games
        self.program_names = program_names
        self.num_bots = len(self.program_names)
        self.game_arity = game_arity
        self.time_limits = time_limits
        self.verbose = verbose
        self.show_map = show_map

        self.results = []
        self.player_lists = []
        self.wins = {p:0 for p in program_names}
        self.placements = {(p,a,i):0 for p in program_names for a in (2,3,4) for i in range(a)}
        self.totals_by_arity = {a:0 for a in (2,3,4)}
        self.diff_results = []
        self.diff_totals_by_arity = {a:0 for a in (2,3,4)}
        self.diff_wins = {p:0 for p in program_names}
        self.diff_placements = {(p,a,i):0 for p in program_names for a in (2,3,4) for i in range(a)}
        self.games_with_errors = {p:[] for p in program_names}
        self.games_with_warnings = {p:[] for p in program_names}
        self.games_played = 0
        self.games_to_look_at = []

        self.start_time = time.perf_counter()

    def generate_random_configurations(self):
        if self.game_arity:
            game_arity = self.game_arity
        else:
            # random arity
            game_arity = random.randrange(2, 5) # 2 <= game_arity <= 4

        num_bots = self.num_bots
        player_order = None
        # get random configuration so that not all one playuer
        while player_order == None or all(i==player_order[0] for i in player_order):
            player_order = [random.randrange(num_bots) for _ in range(game_arity)]

        # Find random starting configuration and encode using CG format
        config_str = ""
        initial_positions = []
        for _ in range(game_arity):
            x = None
            while x == None or (x,y) in initial_positions:
                x = random.randrange(WIDTH)
                y = random.randrange(HEIGHT)
            initial_positions.append((x,y))
            config_str += "({},{})".format(x,y)

        # rotate players to give some semplance of symmetry (esp in 2 bot case)
        random_configs = []
        for i in range(num_bots):
            player_list = [self.program_names[(j+i) % num_bots] for j in player_order]
            random_configs.append((player_list, config_str))

        return random_configs

    def play_game(self, id_number, player_list, config_str):
        try:
            # Initiallization
            game = Game(id_number, config_str, player_list, self.time_limits, self.verbose, self.show_map)

            game.pregame()
            # Game Loop
            while game.is_active():
                # Play one round of the game
                game.one_turn()

            # Handle end of game details
            game.end_of_game()

        except:
            raise
        finally:
            # Kill all subprocesses even if a crash
            for p in game.player_processes:
                if p: p.kill()

        results = tuple(reversed(game.loss_order))
        arity = len(player_list)
        self.results.append(results)
        self.player_lists.append(player_list)
        self.totals_by_arity[arity] += 1
        self.wins[player_list[results[0]]] += 1
        for place, i in enumerate(results):
            player_name = player_list[i]
            self.placements[player_name, arity, place] += 1
        for i, log in enumerate(game.issue_logs):
            player_name = player_list[i]
            if log:
                self.games_with_errors[player_name].append(game.id_number)
        for i, warning_log in enumerate(game.warnings):
            player_name = player_list[i]
            if warning_log:
                self.games_with_warnings[player_name].append(game.id_number)

    def play_all_games(self):
        random_configs = []

        for i in range(self.number_of_games):
            if i % 10 == 0:
                self.print_win_data()

            if not random_configs:
                random_configs = self.generate_random_configurations()

            player_list, config_str = random_configs.pop()
            self.play_game(i, player_list, config_str)
            self.games_played += 1

            if not random_configs:
                # check if all the results of the last set are not the same
                if len(set(self.results[-self.num_bots:])) > 1:
                    self.games_to_look_at.append(tuple(range(i-self.num_bots+1, i+1)))
                    for results, player_list in zip(self.results[-self.num_bots:], self.player_lists[-self.num_bots:]):
                        arity = len(results)
                        self.diff_results.append(results)
                        self.diff_totals_by_arity[arity] += 1
                        self.diff_wins[player_list[results[0]]] += 1
                        for place, i in enumerate(results):
                            player_name = player_list[i]
                            self.diff_placements[player_name, arity, place] += 1


    def print_win_data(self):
        print("==========================")
        print("Tournament Results {}/{} games:".format(self.games_played, self.number_of_games))
        for name in self.program_names:
            error_note = ""
            if self.games_with_errors[name]:
                error_games = ", ".join(map(str, self.games_with_errors[name]))
                error_note += "(Errors on games {}) ".format(error_games)

            if self.games_with_warnings[name]:
                warnings_games = self.games_with_warnings[name]
                if len(warnings_games) > 5:
                    warnings_games = ["..."] + warnings_games[-5:]
                warning_str = ", ".join(map(str, warnings_games))
                error_note += "(Warnings on games {}) ".format(warning_str)
            
            print("{} : {} [{}] wins {}".format(name, self.wins[name], self.diff_wins[name], error_note))

            for arity in (2, 3, 4):
                if self.totals_by_arity[arity]:
                    stats = ["{}. {:3} [{:3}] ".format(i+1, self.placements[name, arity, i], self.diff_placements[name, arity, i]) for i in range(arity)]
                    print("   ", arity, "player games: ", *stats)
        if self.games_to_look_at:
            print("Games where results differ:", *self.games_to_look_at)
        print("Total tournament time:", time.perf_counter() - self.start_time, "sec")

################
# Print helper #
################

def print_side_by_side(stream0, stream1, col_width=80):
    for line0, line1 in itertools.zip_longest(stream0.split('\n'), stream1.split('\n')):
        if line0 == None:
            line0 = ""
        if line1 == None:
            line1 = ""
        print("{1:{0}}{2:{0}}".format(col_width, line0.strip(), line1.strip()))

########
# Main #
########

def main(argv):
    """
    Arguements: tron_arena_bot.py bot1 [bot2] [bot3] [bot4] [-t] [-v] [-m] [-s <config>] [-2|-3|-4] [-n <number>]'
    """
    number_of_games = 10 # Defaults to 10
    time_limits = False
    verbose = False
    show_map = False # Only works if verbose and show_map are both True
    game_arity = None # If set to 2, 3, or 4 it only plays 2, 3, 4 player games
    play_single_game = False
    play_double_game = False

    try:
        opts, args = getopt.gnu_getopt(argv, "tvmn:s:d:234", [])
    except getopt.GetoptError:
        print('tron_arena_bot.py bot1 [bot2] [bot3] [bot4] [-t] [-v] [-m] [-s <config>] [-n <number>] [-2|-3|-4]')
        sys.exit(2)

    #print(argv, opts, args) # for debugging

    if len(args) > 4:
        print("Too many bots.")
        sys.exit(2)

    for opt, arg in opts:
        if opt == '-t': # Turn on time limits
            time_limits = True
        elif opt == '-v': # Show details of each turn
            verbose = True
        elif opt == '-m': # Show game map (assuming -v or -s is set)
            show_map = True
        elif opt in ('-2', '-3', '-4'): # Play <2,3,4> player games only
            n = int(opt[1])
            if len(args) > n:
                print("Too many bots for a", n, "player game.")
                sys.exit(2)
            game_arity = n
        elif opt == '-n': # Set number of games
            number_of_games = int(arg)
        elif opt == '-s': # Play a single game with a particular given .
                          # configuration.  Some other arguments are ignored.
            if play_double_game:
                print("Can't play a single and a double game.")
                sys.exit(2)
            play_single_game = True
            config_str = arg
        elif opt == '-d': # Play a double game with a particular given .
                          # configuration.  It should be called instead of
                          # -s.
            if play_single_game:
                print("Can't play a single and a double game.")
                sys.exit(2)
            elif len(set(args)) != 2:
                print("Double game only works for 2 bots right now.")
                sys.exit(2)
            play_double_game = True
            config_str = arg
            

    if play_single_game or play_double_game:
        player_list = args
        if config_str.count(",") != len(player_list):
            print("Number of bots doesn't match configuration number.")
            sys.exit(2)
        verbose = True

        if play_single_game:
            try:
                # Initiallization
                game = Game(0, config_str, player_list, time_limits, verbose, show_map)

                game.pregame()
                # Game Loop
                while game.is_active():
                    # Play one round of the game
                    game.one_turn()

                # Handle end of game details
                game.end_of_game()

            except:
                raise
            finally:
                # Kill all subprocesses even if a crash
                for p in game.player_processes:
                    if p: p.kill()
        else: # double_game (show side by side)
            player_names = list(set(player_list))
            reverse_player_list = []
            for p in player_list:
                reverse_player_list.append(player_names[1] if p==player_names[0] 
                                           else player_names[0])
            try:
                # Initiallization (don't pass show map)
                game0 = Game(0, config_str, player_list, time_limits, verbose, False)
                game1 = Game(1, config_str, reverse_player_list, time_limits, verbose, False)

                stdout_ = sys.stdout #Keep track of the previous value.
                
                stream0 = io.StringIO()
                sys.stdout = stream0 # capture stdout to a stream
                game0.pregame()
                
                stream1 = io.StringIO()
                sys.stdout = stream1 # capture stdout to a stream
                game1.pregame()

                sys.stdout = stdout_ # restore the previous stdout.
                print_side_by_side(stream0.getvalue(), stream1.getvalue())

                stream0.close()
                stream1.close()

                # Game Loop
                while game0.is_active() or game1.is_active():
                    # Play one round of each game
                    stream0 = io.StringIO()
                    sys.stdout = stream0 # capture stdout to a stream
                    if game0.is_active():
                        game0.one_turn()

                    stream1 = io.StringIO()
                    sys.stdout = stream1 # capture stdout to a stream
                    if game1.is_active():
                        game1.one_turn()

                    sys.stdout = stdout_ # restore the previous stdout.
                    print_side_by_side(stream0.getvalue(), stream1.getvalue())

                    stream0.close()
                    stream1.close()

                    if show_map:
                        stream0 = io.StringIO()
                        sys.stdout = stream0 # capture stdout to a stream
                        game0.tron.debug_grid()

                        stream1 = io.StringIO()
                        sys.stdout = stream1 # capture stdout to a stream
                        game1.tron.debug_grid()

                        sys.stdout = stdout_ # restore the previous stdout.
                        print_side_by_side(stream0.getvalue(), stream1.getvalue())

                        stream0.close()
                        stream1.close()

                
                # Handle end of game details
                stream0 = io.StringIO()
                sys.stdout = stream0 # capture stdout to a stream
                game0.end_of_game()
                
                stream1 = io.StringIO()
                sys.stdout = stream1 # capture stdout to a stream
                game1.end_of_game()

                sys.stdout = stdout_ # restore the previous stdout.
                print_side_by_side(stream0.getvalue(), stream1.getvalue())

                stream0.close()
                stream1.close()

            except:
                raise
            finally:
                # Kill all subprocesses even if a crash
                for p in game0.player_processes:
                    if p: p.kill()
                for p in game1.player_processes:
                    if p: p.kill()


    else:
        program_names = args
        t = Tournament(number_of_games, program_names, game_arity, time_limits, verbose, show_map)
        t.play_all_games()
        t.print_win_data()


if __name__ == "__main__":
    main(sys.argv[1:])
    



