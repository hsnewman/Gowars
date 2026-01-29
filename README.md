GOWARS
Gowars is a reverse engineering project to mimic and revive the historic DECWAR game that was written at the University of Texas at Austin by Bob Hysick and Jeff Potter around 1979.  Care has been taken to have the game mechanics as accurate to the original game as possible.

An online version is available at gowars.net port 1701.

Description:
The code for DECWAR has been lost. Gowars is based on the 2.2 version of the executable and documentation that was released by DECUS.  There are minor differences between the original game and Gowars including:
    * The activate command has additional parameters allowing defining the side your want to be on, if the galaxy is empty what size the galaxy is, how many of each object should be in the galaxy, and the max number of bases per side.
    * The admin command allows for many testing commands
    * The time output includes the time since creation for the galaxy your in
    * The users command outputs information for tcp/ip
    * The type output and type options commands is updated for more information for Gowars
    * For all situational awareness commands (list/bases/planets etc), decwar's information is based on what other ships have "listed".  Gowars mode is based on all objects within range of a friendly ship.
    * The tell command doesn't require a ; after the receiver's name
    * The summary command in pregame shows grand totals of all galaxies
    * The points command is currently not implemented due to the no authentication design of the game.
    * Baud rate is simulated.  In gowars mode baud defaults to 0, while in decwars mode it defaults to 9600.  The Set command supports changing baud to 300, 1200.2400 and 9600, in decwars mode if the user is an administrator they can set their baud to 0.
    * A web interface that shows the each galaxy in "set scan short" mode with hover pop-ups showing that object's status and damages.
    * The code also supports web debugging via pprof, on port 6060
  
    * An improved command line interface:
        * Command history
        * Command line editing
        * Parameter parsing
        * Special characters:
            Enter: Submit command.
            Backspace/Delete: Delete last character.
            Ctrl+A (ASCII 1): Move cursor to beginning of line.
            Ctrl+B (ASCII 2): Move cursor left.
            Ctrl+C(ASCII 3): Cancel command queue and interrupt output.
            Ctrl+E (ASCII 5): Move cursor to end of line.
            Ctrl+F (ASCII 6): Move cursor right.
            Ctrl+K (ASCII 11): Delete to end of line.
            Ctrl+L (ASCII 12): Clears the terminal screen.
            Tab (ASCII 9): Command/parameter completion.
            Escape (ASCII 27): Command completion or repeat last command.
     
Notes:
    * The list command does not support:
        And             Used to separate groups of keywords.
        &               Same as AND.
    * Support for multiple concurrent games at once (with different sizes)
    * An optional modern version (gowars mode) that supports:
        * Tractoring non-ships
        * A different "fog of war".
        * Towing of any object

System design:
    * A basic telnet server along with support for some telent commands
    * An atomic State Engine manages concurrency by running all commands (for a given galaxy) that are state-changing sequentially, while a seperate processor (per ship) runs all non-state-changing commands seperately.
  
Execution:
  Download gowars.go

  go run gowars.go

  Telnet to port localhost:1701

Licensing & Copyright:
Copyright © 2026 Harris S. Newman Consulting

This program is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

This program is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the LICENSE file for more details.

A full copy of the license text is included in the LICENSE (or COPYING) file in this repository.

Contributing
We welcome contributions! To ensure that your contributions can be included under the GPL v3 license:

Fork the repository.

Create a new branch for your feature.

Ensure your new files include the standard GPL v3 header.

Submit a pull request.

By contributing to this project, you agree to license your contribution under the same GPL v3 terms.
