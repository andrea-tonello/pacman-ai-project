# Pacman AI project
The goal of this project is to guide a Pacman agent through various mazes with different rewards.
The project is split in two parts:

- in the 'search' folder, Pacman needs to reach a particular location in the maze while collecting all the food. This is implemented using various algorithms: DFS, BFS, UCS, A*.

- in the 'search_logic' folder, we now instead generate logical sentences describing Pacman physics (movement, eating...). We then use a SAT solver to solve the logical inference tasks associated with *planning* (generating action sequences to reach goal locations and eat all the dots), *localization* (finding oneself on a map, given a local sensor model), *mapping* (building the map from scratch) and *SLAM* (Simultaneous Localization And Mapping).
