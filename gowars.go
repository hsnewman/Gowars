// Copyright © 2026 Harris S. Newman Consulting
//
// This file is part of gowars.
//
// gowars is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

// gowars is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.

// You should have received a copy of the GNU General Public License along with this source code. If not, see <https://www.gnu.org/licenses/>.
package main

import (
	"bufio"
	"context"
	crand "crypto/rand"
	"encoding/binary"
	"encoding/json"
	"fmt"
	"html/template"
	"io"
	"log"
	"math"
	"math/rand"
	"net"
	"net/http"
	"net/http/httputil"
	_ "net/http/pprof"
	"net/url"
	"os"
	"os/signal"
	"runtime"
	"sort"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"syscall"
	"time"

	"github.com/gorilla/websocket"
)

//	Version		Notes
//      0.4.6   list fixed for both decwar and gowar mode
//	0.4.7 - fix shield % in list, range for list
//  	0.4.8 - shield work
//  	0.4.9 - shield transfer. charge 100 for shields up, stardate fixed.
//  	0.4.10 - documentation + pprof (web: http:.//localhost:6060)
//  	0.4.11 - move command work
//  	0.4.12 - move command completion (less tractoring)
//	0.5.0 - impulse work
//	0.5.1 - disturbance work
//	0.5.2 - administrator work
//	0.5.3 - tractor work starts
//	0.5.4 - administrator move completed
//	0.5.5 - work on tractor command line
//	0.5.6 - tractor implementation begins
//  	0.5.7 - integration of tractor into shield up
//  	0.5.8 - add gowars <vpos><hpos> parameter for tractor command
//	0.5.9 - Energy work
// 	0.6.0 - Repair + admin work
//	0.6.1 - Targets
//	0.6.2 - Capture + tordam + fixed race for esc
//	0.6.3 - Phasers completed
//	0.6.4 - Resiliancy - seems resiliant to attackers
//	0.6.5 - Torpedo command start
//      0.6.6 - Torpedo hit
//	0.6.7 - Capture
//	0.6.8 - Build
//	0.6.9 - Dock
//	0.7.0 - Performance issues
//      0.7.1 - Messages cleanup
//	0.7.2 - Destruction checking/star novas
//	0.7.3 - Final testing of commands
//      0.8.0 - Robots turns
//	0.9.0 - Tuning/concurrency
//	0.9.1 - Hit tuning
//	0.9.2 - Fixed tractor on exit, more tuning
//  	0.9.3 - God web view
//	0.9.4 - Fix control-c handling in game-state-changing commands
//	0.9.5 - Revised summary command and behavior
//	0.9.6 - Audit phaser and torpedo commands against decwar
//	0.9.7 - Remove dead code and obvious duplication, clean up
//      0.9.8 - Output cleanup to match decwar
//	0.9.9 - Mobile mode & cleanup
//
//	Command Status:
//	Pregame:
//	Activate:
//	Gripe - Done
//	Help: - Done
//	News: - Done
//	Points:
//	Quit: - Done
//	Set: 	Done
//	Summary: Done
//	Time: 	Done
//	Users: Done
//
//	game:
//	Admin - In process
//	BAses - DONE (summary on all sub-commands implemented, 'all sum' shows only counts), also is listing location out of range
//	BUild
//	Capture
//	DAmages - needs formatting
//	DOck
//	Energy - done
//	Gripe - Done
//	Help - Done
//	Impulse - done
//	List - Done
//	Move - done
//	News - Done
//	PHasers
//	PLanets - done
//	Quit  - Done
//	RAdio  - Done
//	REpair - done
//	SCan - Done
//	SEt - Done
//	SHields - Done
//	SRscan - Done
//	STatus - Done
//	SUmmary - Done (needs formatting)
//	TArgets - Done
//	TEll - Done
//	TIme - Done
//	TOrpedoes
//	TRactor - done
//	TYpe - Done
//	Users - Done
//	romulans and other robots support
//

// Helper to set destruction cooldown for a connection
func (i *Interpreter) setDestructionCooldownForConn(connInfo ConnectionInfo, galaxy uint16) {
	i.destroyedCooldownsMutex.Lock()
	defer i.destroyedCooldownsMutex.Unlock()
	if i.destroyedCooldowns == nil {
		i.destroyedCooldowns = make(map[string]map[uint16]time.Time)
	}
	key := connInfo.IP + ":" + connInfo.Port
	if _, ok := i.destroyedCooldowns[key]; !ok {
		i.destroyedCooldowns[key] = make(map[uint16]time.Time)
	}
	i.destroyedCooldowns[key][galaxy] = time.Now()
}

// Admin help text for reuse in handler and prompt
const adminHelpText = "Admin command: set ship system damage, status, or password.\r\n" +
	"Parameters:\r\n" +
	"  ShieldsDamage <value>      - Set shields damage\r\n" +
	"  WarpDamage <value>         - Set warp engines damage\r\n" +
	"  ImpulseDamage <value>      - Set impulse engines damage\r\n" +
	"  LifeSupport <value>        - Set life support damage\r\n" +
	"  TorpDamage <value>         - Set torpedo tube damage\r\n" +
	"  PhaserDamage <value>       - Set phaser damage\r\n" +
	"  ComputerDamage <value>     - Set computer damage\r\n" +
	"  RadioDamage <value>        - Set radio damage\r\n" +
	"  TractorDamage <value>      - Set tractor damage\r\n" +
	"  ShieldEnergy <value>       - Set shield energy\r\n" +
	"  ShipEnergy <value>         - Set ship energy\r\n" +
	"  NumTorps <value>           - Set number of torpedos\r\n" +
	"  Password <string value>    - Set admin mode\r\n" +
	"  Create <type> <vpos> <hpos> - Create object at coordinates (uses ICdef)\r\n" +
	"  Beam <obj-vpos><obj-hpos> <vpos><hpos> - Move any object from one location to another\r\n" +
	"  Status <X> <Y>             - Show status of object at coordinates X,Y\r\n" +
	"  Damages <X> <Y>            - Show damage status of object at coordinates X,Y\r\n" +
	"  Runtime                    - Show Go runtime statistics\r\n" +
	"  ShipDamage <value>         - Set the ship's damage\r\n" +
	"Object types: star, planet, base, blackhole, romulan (can be abbreviated)\r\n" +
	"Example: admin ShieldsDamage 10\r\n" +
	"Example: admin ShieldEn 500\r\n" +
	"Example: admin NumTorps 8\r\n" +
	"Example: admin Password YourBestGuess\r\n" +
	"Example: admin Create st 1 1\r\n" +
	"Example: admin Create planet 5 10\r\n" +
	"Example: admin Move 12 34\r\n" +
	"Example: admin Beam 12 34 56 78\r\n" +
	"Example: admin Status 12 34\r\n" +
	"Example: admin Damages 12 34\r\n" +
	"Example: admin Runtime"

const gowarVersion = "[GOWARs Version 0.9.9 24-Feb-26]\r\n"
const gowarVersionDW = "[Decwar Version 2.2 emulation under GOWARs Version 0.9.9 24-Feb-26]\r\n"

// galaxyEnqueueTimeout is the maximum time ExecuteCombined (and the single-command
// routing path) will block waiting for a galaxy's CommandQueue to accept a new
// task before returning a user-visible error.  Raise this value if very long
// commands make the queue transiently full under normal load; lower it if you
// prefer faster failure feedback to players.
const galaxyEnqueueTimeout = 5 * time.Second

// startShipCommandProcessor launches a goroutine to process commands for a single ship/player.
func (i *Interpreter) startShipCommandProcessor(conn net.Conn, info *ConnectionInfo) {
	go func() {
		for task := range info.CommandQueue {
			// Check for context cancellation before executing the command
			select {
			case <-task.Context.Done():
				task.Response <- "[Output interrupted]"
				continue
			default:
			}
			// Only delay for commands that require it
			if task.RequiresDelay {
				time.Sleep(task.DelayDuration)
			}
			// Check again after delay, in case it was cancelled during sleep
			select {
			case <-task.Context.Done():
				task.Response <- "[Output interrupted]"
				continue
			default:
			}
			result := i.executeCommand(task)
			task.Response <- result
		}
	}()
}

/*
Command Routing System:
- Game-state-changing commands (move, combat, repairs, etc.) go through StartStateEngine for atomic processing
- Non-state-changing commands (help, status, scan, etc.) use per-ship processors for better performance
- This ensures game state consistency while maintaining good response times for read-only operations
*/

// Package-level lookup tables for isGameStateChangingCommand, created once
// instead of on every call.
var gameStateCommands = map[string]bool{
	"move":      true,
	"phasers":   true,
	"torpedoes": true,
	"torpedo":   true,
	"capture":   true,
	"build":     true,
	"dock":      true,
	"energy":    true,
	"impulse":   true,
	"repair":    true,
	"shields":   true,
	"tractor":   true,
	"radio":     true,
	"activate":  true, // Creates/modifies galaxy state
	"quit":      true, // Removes ships and cleans up tractor beams
}

var gameStateSetParams = map[string]bool{
	"shieldsdamage":  true,
	"warpdamage":     true,
	"impulsedamage":  true,
	"lifesupport":    true,
	"torpdamage":     true,
	"phaserdamage":   true,
	"computerdamage": true,
	"radiodamage":    true,
	"tractordamage":  true,
	"shipdamage":     true,
	"shipcondition":  true,
	"shieldenergy":   true,
	"shipenergy":     true,
	"numtorps":       true,
}

var gameStateAdminParams = map[string]bool{
	"beam":    true, // Moves objects
	"create":  true, // Creates objects
	"destroy": true, // Destroys objects
}

// isGameStateChangingCommand determines if a command changes game state and should go through StartStateEngine
func (i *Interpreter) isGameStateChangingCommand(command string) bool {
	// Extract the first word of the command
	fields := strings.Fields(strings.ToLower(command))
	if len(fields) == 0 {
		return false
	}

	cmdName := fields[0]

	// Resolve abbreviations so "tor" becomes "torpedoes"
	if full, ok := i.resolveCommand(cmdName, "gowars"); ok {
		cmdName = full
	} else if full, ok := i.resolveCommand(cmdName, "pregame"); ok {
		cmdName = full
	}

	// Special handling for set command - only game-state-changing if modifying ship stats
	if cmdName == "set" && len(fields) >= 2 {
		return gameStateSetParams[fields[1]]
	}

	// Special handling for admin command - only game-state-changing for certain operations
	if cmdName == "admin" && len(fields) >= 2 {
		// Resolve abbreviation of the admin sub-command (e.g. "cre" -> "create")
		adminParam := fields[1]
		for key := range gameStateAdminParams {
			if strings.HasPrefix(key, adminParam) {
				adminParam = key
				break
			}
		}
		return gameStateAdminParams[adminParam]
	}

	return gameStateCommands[cmdName]
}

// Telnet protocol constants
const (
	IAC      = 255 // Interpret As Command
	DONT     = 254
	DO       = 253
	WONT     = 252
	WILL     = 251
	AYT      = 246 // Are You There
	SIGQUIT  = 243 // Telnet SIGQUIT command
	ECHO     = 1
	LINEMODE = 34
	ESC      = 27 // Escape key
)

// Configuration constants
const (
	MaxGalaxies          = 1024
	MaxSizeX             = 75
	MaxSizeY             = 75
	MaxBlackHoles        = 20
	MaxNeutralPlanets    = 20
	MaxFederationPlanets = 10
	MaxEmpirePlanets     = 10
	MaxStars             = 150
	MaxBasesPerSide      = 10
	MaxRomulans          = 5
	DefScanRange         = 20
	BoardStart           = 1
	ServerPort           = 1701
	WebServerPort        = 1702
	TelnetWebPort        = 1703
	ReverseProxyPort     = 443
	MaxIdleTime          = 10
	DefaultBaudRate      = 9600
	DecwarMode           = true
	InitialShieldValue   = 25000
	InitialShipEnergy    = 50000
	CostFactor           = 40
	CriticalDamage       = 300
	CriticalShipDamage   = 250000
	MaxRange             = 10
	DecwarModeMaxUsers   = 28000 //Maximum is due to # ports available, 3 used per user
	goWarsModeMaxUsers   = 20000 //Maximum is due to # ports available, 3 used per user
	MaxInputLength       = 1024  // Maximum length of input buffer to prevent memory exhaustion
	MaxStackedCommands   = 10    // Maximum number of stacked commands per line (e.g., cmd1/cmd2/cmd3)
)

// Return a + or - based on ShieldsUpDown
func boolToSign(shieldsign bool) string {
	if shieldsign {
		return "+"
	}
	return "-"
}

// sanitizeName validates and sanitizes a player name.
// It rejects ANSI escape sequences, control characters, and non-printable ASCII.
// Returns the sanitized name and an error message if invalid.
// Maximum length is 12 characters, consistent with classic decwar.
func sanitizeName(name string) (string, string) {
	const maxNameLength = 12

	// Check for empty name
	if len(name) == 0 {
		return "", "Error: name cannot be empty"
	}

	// Check length
	if len(name) > maxNameLength {
		return "", "Error: name must be at most 12 characters"
	}

	// Validate each character - only allow printable ASCII (0x20-0x7E)
	// This rejects:
	// - Control characters (< 0x20) including ANSI escape sequences (\x1b)
	// - DEL character (0x7F)
	// - Extended ASCII (> 0x7F)
	for i, c := range name {
		if c < 0x20 || c > 0x7E {
			return "", fmt.Sprintf("Error: name contains invalid character at position %d (only printable ASCII allowed)", i+1)
		}
	}

	// Check for ESC character specifically (part of ANSI sequences)
	if strings.ContainsRune(name, '\x1b') {
		return "", "Error: name cannot contain escape sequences"
	}

	return name, ""
}

// sanitizeGripeText sanitizes gripe text by removing control characters
// and limiting length to 1024 characters.
func sanitizeGripeText(text string) string {
	const maxGripeLength = 1024

	// Build sanitized string, removing control characters
	var sanitized strings.Builder
	for _, c := range text {
		// Allow printable ASCII (0x20-0x7E) and common whitespace (space, but not other control chars)
		if c >= 0x20 && c <= 0x7E {
			sanitized.WriteRune(c)
		} else if c == '\t' {
			// Convert tabs to spaces
			sanitized.WriteRune(' ')
		}
		// Skip all other control characters including ESC, newlines, etc.
	}

	result := sanitized.String()

	// Limit length
	if len(result) > maxGripeLength {
		result = result[:maxGripeLength]
	}

	return strings.TrimSpace(result)
}

// rotateGripeFile checks if gripe.txt exceeds maxSize (1MB) and truncates
// the oldest entries if necessary to keep the file under the limit.
const maxGripeFileSize = 1024 * 1024 // 1MB

func rotateGripeFile(filename string) error {
	info, err := os.Stat(filename)
	if os.IsNotExist(err) {
		return nil // File doesn't exist yet, nothing to rotate
	}
	if err != nil {
		return err
	}

	if info.Size() <= maxGripeFileSize {
		return nil // File is under the limit
	}

	// Read the file
	data, err := os.ReadFile(filename)
	if err != nil {
		return err
	}

	// Keep only the most recent entries that fit within the size limit
	// We'll keep approximately 90% of the max size to avoid frequent rotations
	targetSize := (maxGripeFileSize * 9) / 10

	if len(data) <= targetSize {
		return nil
	}

	// Find a newline boundary to cut at, keeping the newer (end) portion
	cutPoint := len(data) - targetSize
	for cutPoint < len(data) && data[cutPoint] != '\n' {
		cutPoint++
	}
	if cutPoint < len(data) {
		cutPoint++ // Skip past the newline
	}

	// Write back the truncated file
	return os.WriteFile(filename, data[cutPoint:], 0644)
}

// getPathCells returns the grid cells along a line from (startX,startY) to
// (targetX,targetY) using Bresenham's algorithm.  displ applies a navigation
// error offset when the computer is damaged.
func getPathCells(startX, startY, targetX, targetY int, dist int, displ float32) ([][2]int, int, int) {
	var sum float32
	// Nav error - computer down can cause target jitter
	if AbsInt(targetX-startX) > AbsInt(targetY-startY) {
		if displ > 0 {
			sum = float32(targetY) - displ + 0.33
		} else {
			sum = float32(targetY) + displ - 0.33
		}
		targetY = int(math.Round(float64(sum)))
	} else {
		if displ > 0 {
			sum = float32(targetX) - displ + 0.33
		} else {
			sum = float32(targetX) + displ - 0.33
		}
		targetX = int(math.Round(float64(sum)))
	}

	cells := make([][2]int, 0, dist)
	dx := targetX - startX
	dy := targetY - startY
	steps := max(AbsInt(dx), AbsInt(dy)) // Use Manhattan for grid steps; adjust for Euclidean if needed
	if steps == 0 {
		return cells, targetX, targetY
	}
	stepX := float64(dx) / float64(steps)
	stepY := float64(dy) / float64(steps)
	curX, curY := float64(startX), float64(startY)
	for i := 1; i <= steps; i++ { // Start from 1 to skip starting position
		curX += stepX
		curY += stepY
		cellX := int(math.Round(curX))
		cellY := int(math.Round(curY))
		cells = append(cells, [2]int{cellX, cellY})
	}
	return cells, targetX, targetY
}

// newSeededRand creates a new *rand.Rand seeded from crypto/rand.
// Falls back to time-based seeding if the OS entropy source is unavailable.
func newSeededRand() *rand.Rand {
	var seed int64
	if err := binary.Read(crand.Reader, binary.LittleEndian, &seed); err != nil {
		seed = time.Now().UnixNano()
	}
	return rand.New(rand.NewSource(seed))
}

// RandomInt returns a random integer between 0 (inclusive) and max (exclusive).
// Uses a per-call throwaway RNG; callers with galaxy context should prefer
// galaxy.rng directly to avoid allocation.
func RandomInt(max int) int {
	return newSeededRand().Intn(max)
}

// StartStateEngine is the atomic processor that handles all game state modifications
// StartStateEngine now acts as a safety-net forwarder. Any tasks that arrive on
// the legacy global TaskQueue are forwarded to the appropriate per-galaxy
// CommandQueue. This ensures backward compatibility if any code path still
// sends to i.TaskQueue directly.
func (i *Interpreter) StartStateEngine() {
	i.stateEngineRunning = true
	defer func() { i.stateEngineRunning = false }()

	log.Printf("State Engine started (per-galaxy forwarder mode)")
	for {
		select {
		case task := <-i.TaskQueue:
			// Forward task to the appropriate per-galaxy command queue
			log.Printf("StartStateEngine: Forwarding task '%s' from player %s to galaxy %d queue",
				task.Command, task.PlayerID, task.Galaxy)

			galaxy := i.getOrCreateGalaxy(task.Galaxy)
			select {
			case galaxy.CommandQueue <- task:
				// Successfully forwarded
				log.Printf("StartStateEngine: Task forwarded to galaxy %d queue", task.Galaxy)
			case <-i.shutdown:
				log.Printf("StartStateEngine: Shutdown during forward, dropping task for player %s", task.PlayerID)
				task.Response <- "[Server shutting down]"
				return
			}

		case <-i.shutdown:
			log.Printf("State Engine forwarder shutting down")
			return
		}
	}
}

// executeCommand processes a single command without any external locking
func (i *Interpreter) executeCommand(task *GameTask) string {
	// This replaces the logic from runCommandWithContext but without mutex usage
	// Handle special ESC completion command
	if strings.HasPrefix(task.Command, "ESC_COMPLETE:") {
		prefix := strings.TrimPrefix(task.Command, "ESC_COMPLETE:")
		section := "pregame"
		if info, ok := i.connections.Load(task.Conn); ok {
			connInfo := info.(ConnectionInfo)
			section = connInfo.Section
		}

		completions := i.getCompletions(prefix, section, task.Conn)
		switch len(completions) {
		case 0:
			return fmt.Sprintf("Invalid input: '%s'", prefix)
		case 1:
			return completions[0]
		default:
			return strings.Join(completions, "\r\n")
		}
	}

	section := "pregame"
	if info, ok := i.connections.Load(task.Conn); ok {
		connInfo := info.(ConnectionInfo)
		section = connInfo.Section
	}

	var parts []string
	if section == "pregame" && (strings.HasPrefix(task.Command, "gripe ") || task.Command == "gripe") {
		parts = []string{"gripe"}
		if len(task.Command) > len("gripe ") {
			gripeArg := strings.TrimPrefix(task.Command, "gripe ")
			parts = append(parts, gripeArg)
		}
	} else {
		parts = strings.Fields(task.Command)
	}

	if len(parts) == 0 {
		return ""
	}

	cmd := strings.ToLower(parts[0])
	args := parts[1:]

	var handler CommandHandler
	var fullCmd string
	var ok bool

	if section == "pregame" {
		fullCmd, ok = i.resolveCommand(cmd, "pregame")
		if ok {
			handler = i.pregameCommands[fullCmd].Handler
		}
	} else {
		fullCmd, ok = i.resolveCommand(cmd, "gowars")
		if ok {
			handler = i.gowarsCommands[fullCmd].Handler
		}
	}

	if !ok {
		return fmt.Sprintf("Invalid command: %s", cmd)
	}

	// If handler supports context, call with context
	type ctxHandler func(context.Context, []string, net.Conn) string
	if h, ok := any(handler).(ctxHandler); ok {
		return h(task.Context, args, task.Conn)
	}

	// For specific commands that produce long output, use context-aware versions
	switch fullCmd {
	case "scan":
		return i.handleScanCtx(task.Context, DefScanRange, args, task.Conn)
	case "srscan":
		return i.handleScanCtx(task.Context, 14, args, task.Conn)
	case "status":
		return i.handleStatusCtx(task.Context, args, task.Conn)
	case "list":
		return i.handleListCtx(task.Context, args, task.Conn)
	case "targets":
		return i.handleTargetsCtx(task.Context, args, task.Conn)
	case "damages":
		return i.handleDamagesCtx(task.Context, args, task.Conn)
	default:
		return handler(args, task.Conn)
	}
}

// ExecuteCombined processes a chain of commands separated by "/" ensuring proper state synchronization
//
// IMPLEMENTATION:
// 1. ExecuteCombined processes each command sequentially
// 2. Each command waits for completion via response channel before proceeding
// 3. SyncShipState() ensures all pending state changes are flushed between commands
// 4. Guarantees: Move completes entirely -> State synchronized -> Scan reads consistent state
func (i *Interpreter) ExecuteCombined(command string, conn net.Conn, writer *bufio.Writer, ctx context.Context) {
	parts := strings.Split(command, "/")
	interrupted := false
	firstCommand := true

	// Limit the number of stacked commands to prevent abuse
	if len(parts) > MaxStackedCommands {
		i.writeBaudfCtx(ctx, conn, writer, "\r\nToo many stacked commands (max %d). Command line rejected.\r\n", MaxStackedCommands)
		return
	}

	for idx, cmdStr := range parts {
		// Check for context cancellation before processing each command
		select {
		case <-ctx.Done():
			interrupted = true
			break
		default:
		}
		if interrupted {
			break
		}
		cmdStr = strings.TrimSpace(cmdStr)
		if cmdStr == "" {
			continue
		}

		// Get player info for the task
		var playerID string
		var galaxy uint16
		if info, ok := i.connections.Load(conn); ok {
			connInfo := info.(ConnectionInfo)
			playerID = connInfo.Shipname
			galaxy = connInfo.Galaxy
			if playerID == "" {
				playerID = connInfo.IP // Use IP as fallback for pregame
			}
		}

		// Create response channel
		response := make(chan string, 1)

		// Create game task with IsStateChanging flag
		task := &GameTask{
			PlayerID:        playerID,
			Command:         cmdStr,
			Galaxy:          galaxy,
			Conn:            conn,
			Writer:          writer,
			Context:         ctx,
			Response:        response,
			IsStateChanging: i.isGameStateChangingCommand(cmdStr),
		}

		// Process each command and wait for completion before proceeding
		if interrupted {
			break
		}

		// Print "Command: " prompt before each stacked command after the first
		if !firstCommand {
			prompt := i.getPrompt(conn)
			if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
				mutex := mutexRaw.(*sync.Mutex)
				mutex.Lock()
				fmt.Fprintf(writer, "\r%-79s\r%s", "", prompt)
				writer.Flush()
				mutex.Unlock()
			}
		}
		firstCommand = false

		// Route to the per-galaxy command queue for parallel processing.
		// Block up to galaxyEnqueueTimeout for the queue to accept the task so
		// that a momentarily-busy galaxy engine does not silently discard the
		// player's command.  Only return an error to the player after the
		// timeout has elapsed.
		galaxyObj := i.getOrCreateGalaxy(galaxy)
		log.Printf("ExecuteCombined: Routing command '%s' (%d/%d) for player %s to galaxy %d queue (state-changing: %v)",
			cmdStr, idx+1, len(parts), playerID, galaxy, task.IsStateChanging)
		enqueueCtx, enqueueCancel := context.WithTimeout(ctx, galaxyEnqueueTimeout)
		select {
		case galaxyObj.CommandQueue <- task:
			enqueueCancel()
			// Wait for command to complete before proceeding
			result := <-response
			if result != "" {
				i.writeBaudfCtx(ctx, conn, writer, "\r\n%s\r\n", result)
			}

			// Check for context cancellation after command completes
			select {
			case <-ctx.Done():
				interrupted = true
				break
			default:
			}
			if interrupted {
				break
			}

		case <-ctx.Done():
			enqueueCancel()
			interrupted = true
			i.writeBaudfCtx(ctx, conn, writer, "\r\n[Output interrupted]\r\n")
			break
		case <-enqueueCtx.Done():
			enqueueCancel()
			i.writeBaudfCtx(ctx, conn, writer,
				"\r\nGalaxy %d engine busy; command '%s' could not be queued after %s — please try again.\r\n",
				galaxy, cmdStr, galaxyEnqueueTimeout)
			break
		}
	}

	if interrupted {
		i.writeBaudfCtx(ctx, conn, writer, "\r\n[Remaining stacked commands discarded]\r\n")
	}

	// Re-render prompt after all commands complete or interruption
	prompt := i.getPrompt(conn)
	if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
		mutex := mutexRaw.(*sync.Mutex)
		mutex.Lock()
		fmt.Fprintf(writer, "\r%-79s\r%s", "", prompt)
		writer.Flush()
		mutex.Unlock()
	}
}

// BatchDone returns a channel that is closed by processGalaxyCommands immediately
// after it finishes the current task batch (command + robots + spatial rebuild).
// Callers that need a happens-before guarantee should receive on this channel
// instead of sleeping.  A fresh channel is installed before the old one is closed
// so that new waiters always get the *next* completion event.
func (g *Galaxy) BatchDone() <-chan struct{} {
	g.syncDoneMu.Lock()
	defer g.syncDoneMu.Unlock()
	if g.syncDone == nil {
		g.syncDone = make(chan struct{})
	}
	return g.syncDone
}

// signalBatchDone closes the current syncDone channel (waking all waiters) and
// installs a fresh one for the next batch.  Called by processGalaxyCommands
// after each task completes, while galaxy.Mutex is still held.
func (g *Galaxy) signalBatchDone() {
	g.syncDoneMu.Lock()
	old := g.syncDone
	g.syncDone = make(chan struct{})
	g.syncDoneMu.Unlock()
	if old != nil {
		close(old)
	}
}

// SyncShipState waits until the GalaxyEngine signals that it has finished
// processing the current task batch, providing a true happens-before guarantee
// with zero busy-waiting.  It replaces the previous implementation that called
// time.Sleep twice and acquired/released galaxy.Mutex as a flush trick.
func (i *Interpreter) SyncShipState(galaxy uint16) {
	i.rebuildSpatialIndexes()

	if galaxy > 0 {
		i.galaxiesMutex.RLock()
		galaxyObj, ok := i.galaxies[galaxy]
		i.galaxiesMutex.RUnlock()
		if ok && galaxyObj != nil {
			// Block until the engine signals completion of the current batch.
			done := galaxyObj.BatchDone()
			<-done
		}
	}

	log.Printf("SyncShipState: State synchronized for galaxy %d", galaxy)
}

// syncShipStateWithinGalaxy is called from within processGalaxyCommands while
// galaxy.Mutex is already held.  It only rebuilds spatial indexes; the
// happens-before guarantee for external callers is provided by signalBatchDone
// (called after this function returns and the mutex is released).
func (i *Interpreter) syncShipStateWithinGalaxy(galaxy uint16) {
	// Rebuild spatial indexes to ensure consistency after movement or state change
	i.rebuildSpatialIndexes()

	log.Printf("syncShipStateWithinGalaxy: State synchronized for galaxy %d", galaxy)
}

// getPlayerSide determines the player's side for robot processing
func (i *Interpreter) getPlayerSide(playerID string, galaxy uint16) string {
	i.spatialIndexMutex.RLock()
	defer i.spatialIndexMutex.RUnlock()
	// Find the player's ship to determine their side
	for _, obj := range i.objects {
		if obj.Galaxy == galaxy && obj.Type == "Ship" && obj.Name == playerID {
			return obj.Side
		}
	}
	return ""
}

// Shutdown gracefully stops the state engine
func (i *Interpreter) Shutdown() {
	// Close the global shutdown channel, which signals both the
	// StartStateEngine forwarder and all per-galaxy processGalaxyCommands
	// goroutines to exit cleanly.
	close(i.shutdown)
}

// broadcastWorldState sends updates to all players in a galaxy
func (i *Interpreter) broadcastWorldState(galaxy uint16) {
	// This can be implemented later for real-time updates
	// For now, it's a stub
}

// delayCall holds parameters for a deferred delayPause invocation collected
// during robotsUnlocked so they can be fired after iteration completes.
type delayCall struct {
	conn              net.Conn
	numberMillisecond int
	galaxy            uint16
	callerType        string
	callerSide        string
}

// findConnectionForShip looks up the net.Conn associated with a ship name in
// a given galaxy.  Returns nil if no matching connection is found.
func (i *Interpreter) findConnectionForShip(shipName string, galaxy uint16) net.Conn {
	var found net.Conn
	i.connections.Range(func(key, value interface{}) bool {
		ci := value.(ConnectionInfo)
		if ci.Shipname == shipName && ci.Galaxy == galaxy {
			found = key.(net.Conn)
			return false
		}
		return true
	})
	return found
}

// isEnemyTarget returns true when target is an enemy of defender.
// Neutral defenders (planets) consider everyone an enemy; otherwise the two
// opposing factions and romulans are enemies.
func isEnemyTarget(defenderSide, targetSide string) bool {
	if targetSide == "romulan" {
		return true
	}
	if defenderSide == "neutral" {
		return true
	}
	if defenderSide == "federation" && targetSide == "empire" {
		return true
	}
	if defenderSide == "empire" && targetSide == "federation" {
		return true
	}
	return false
}

// handlePhaserDefenseAttack fires a phaser attack from attacker at target,
// broadcasts the combat event, and—if the target is destroyed—appends a
// destruction delay call.  Returns the (possibly grown) pendingDelayCalls slice.
func (i *Interpreter) handlePhaserDefenseAttack(attacker, target *Object, energy int, pending []delayCall) []delayCall {
	evt, err := i.phaserAttack(attacker, target, energy)
	if err != nil || evt == nil {
		return pending
	}
	i.BroadcastCombatEventNoLock(evt)
	if evt.Message == "destroyed" {
		dlypse := calculateDlypse(300, 1, 1, 6, 6)
		conn := i.findConnectionForShip(target.Name, target.Galaxy)
		pending = append(pending, delayCall{
			conn:              conn,
			numberMillisecond: dlypse,
			galaxy:            attacker.Galaxy,
			callerType:        target.Type,
			callerSide:        target.Side,
		})
	}
	return pending
}

// findEnemyShipsInRange returns all enemy Ship objects from objectsCopy that
// are within maxRange of defender.
func findEnemyShipsInRange(objectsCopy []*Object, defender *Object, galaxy uint16, maxRange int) []*Object {
	var targets []*Object
	for _, target := range objectsCopy {
		if target.Galaxy != galaxy || target.Type != "Ship" {
			continue
		}
		rangeDist := max(AbsInt(target.LocationX-defender.LocationX), AbsInt(target.LocationY-defender.LocationY))
		if rangeDist <= maxRange && isEnemyTarget(defender.Side, target.Side) {
			targets = append(targets, target)
		}
	}
	return targets
}

// robotsUnlocked function updated to work without mutex (called from atomic processor)
func (i *Interpreter) robotsUnlocked(galaxy uint16, callerSide string) {
	// --- ROMULAN MOVEMENT PASS ---
	type romMove struct {
		ship    *Object
		targetX int
		targetY int
	}

	// Collect pending delay calls to prevent recursive iteration issues
	var pendingDelayCalls []delayCall
	var romulanMoves []*Object
	var romulanTargets []romMove

	// Create a safe copy of object pointers under RLock to prevent index out of range
	// during iteration. With per-galaxy parallelism, another galaxy goroutine can
	// shrink i.objects between reading len() and accessing elements.
	i.spatialIndexMutex.RLock()
	objectsCopy := make([]*Object, len(i.objects))
	copy(objectsCopy, i.objects)
	i.spatialIndexMutex.RUnlock()

	for _, obj := range objectsCopy {
		if obj.Galaxy == galaxy && obj.Type == "Ship" && obj.Side == "romulan" {
			// Directed pursuit: find nearest federation/empire ship or starbase (decwar style)
			const romMaxMove = 4 // max sectors per turn toward target
			var nearestTarget *Object
			nearestDist := math.MaxInt

			for _, candidate := range objectsCopy {
				if candidate.Galaxy != galaxy {
					continue
				}
				// Targets: federation or empire ships, or starbases
				isTargetShip := candidate.Type == "Ship" &&
					(candidate.Side == "federation" || candidate.Side == "empire")
				isTargetBase := candidate.Type == "Base" &&
					(candidate.Side == "federation" || candidate.Side == "empire")
				if !isTargetShip && !isTargetBase {
					continue
				}
				// Chebyshev distance (same metric used elsewhere in game)
				dist := max(AbsInt(candidate.LocationX-obj.LocationX),
					AbsInt(candidate.LocationY-obj.LocationY))
				if dist < nearestDist {
					nearestDist = dist
					nearestTarget = candidate
				}
			}

			_, galaxyMaxX, galaxyMaxY := i.validateGalaxyBoundaries(galaxy, obj.LocationX, obj.LocationY)
			var targetX, targetY int

			if nearestTarget != nil {
				// Calculate offset toward nearest target, capped at romMaxMove per axis
				dx := nearestTarget.LocationX - obj.LocationX
				dy := nearestTarget.LocationY - obj.LocationY
				log.Printf("[Romulan pursuit] %s at (%d,%d) targeting %s at (%d,%d) dx=%d dy=%d",
					obj.Name, obj.LocationX, obj.LocationY,
					nearestTarget.Name, nearestTarget.LocationX, nearestTarget.LocationY, dx, dy)
				if dx > romMaxMove {
					dx = romMaxMove
				} else if dx < -romMaxMove {
					dx = -romMaxMove
				}
				if dy > romMaxMove {
					dy = romMaxMove
				} else if dy < -romMaxMove {
					dy = -romMaxMove
				}
				targetX = obj.LocationX + dx
				targetY = obj.LocationY + dy
			} else {
				// No valid target: fall back to random walk
				log.Printf("[Romulan pursuit] %s at (%d,%d) - no target found, random walk",
					obj.Name, obj.LocationX, obj.LocationY)
				targetX = obj.LocationX + RandomInt(13) - 6
				targetY = obj.LocationY + RandomInt(13) - 6
			}

			// Clamp to galaxy bounds
			if targetX < 1 {
				targetX = 1
			}
			if targetX > galaxyMaxX {
				targetX = galaxyMaxX
			}
			if targetY < 1 {
				targetY = 1
			}
			if targetY > galaxyMaxY {
				targetY = galaxyMaxY
			}
			log.Printf("[Romulan pursuit] %s moving from (%d,%d) to (%d,%d)",
				obj.Name, obj.LocationX, obj.LocationY, targetX, targetY)
			romulanMoves = append(romulanMoves, obj)
			romulanTargets = append(romulanTargets, romMove{ship: obj, targetX: targetX, targetY: targetY})
		}
	}

	for _, move := range romulanTargets {
		i.moveShip(move.ship, move.targetX, move.targetY, "warp", nil)
	}

	// --- ROMULAN ATTACK PASS ---
	for _, romulan := range romulanMoves {
		// Create a list of potential targets within range
		var targets []*Object
		targetTypes := []string{"Ship", "Base", "Planet", "Star"}
		for _, targetType := range targetTypes {
			objects := i.getObjectsByType(galaxy, targetType)
			if objects != nil {
				for _, target := range objects {
					if target.Side == "romulan" {
						continue
					}
					rangeDist := max(AbsInt(target.LocationX-romulan.LocationX), AbsInt(target.LocationY-romulan.LocationY))
					if rangeDist <= MaxRange {
						targets = append(targets, target)
					}
				}
			}
		}
		if len(targets) == 0 {
			continue
		}

		weaponChoice := RandomInt(2)
		var selectedTarget *Object
		if weaponChoice == 0 {
			selectedTarget = targets[RandomInt(len(targets))]
		} else {
			var nonStarTargets []*Object
			for _, target := range targets {
				if target.Type != "Star" {
					nonStarTargets = append(nonStarTargets, target)
				}
			}
			if len(nonStarTargets) == 0 {
				continue
			}
			selectedTarget = nonStarTargets[RandomInt(len(nonStarTargets))]
		}

		if weaponChoice == 0 {
			numTorps := RandomInt(3) + 1
			_, err := i.torpedoAttack(romulan, selectedTarget.LocationX, selectedTarget.LocationY, numTorps, nil)
			if err == nil {
				// Find attacker and target indices for combat event
				attackerIdx := -1
				targetIdx := -1
				i.spatialIndexMutex.RLock()
				for tidx, objPtr := range i.objects {
					if objPtr == romulan {
						attackerIdx = tidx
					}
					if objPtr == selectedTarget {
						targetIdx = tidx
					}
					if attackerIdx != -1 && targetIdx != -1 {
						break
					}
				}
				i.spatialIndexMutex.RUnlock()
				if attackerIdx != -1 && targetIdx != -1 {
					i.BroadcastCombatEventNoLock(&CombatEvent{
						Galaxy:      galaxy,
						AttackerIdx: attackerIdx,
						TargetIdx:   targetIdx,
						Weapon:      "Torpedo",
						Damage:      0,
						Message:     "hit",
					})
				}
			}
		} else {
			energy := RandomInt(151) + 50
			pendingDelayCalls = i.handlePhaserDefenseAttack(romulan, selectedTarget, energy, pendingDelayCalls)
		}
	}

	// --- BASE ENERGY REBUILD ---
	var basePtrs []*Object
	for _, obj := range objectsCopy {
		if obj.Galaxy == galaxy && obj.Type == "Base" {
			basePtrs = append(basePtrs, obj)
		}
	}

	var oppositeSide string
	if callerSide == "federation" {
		oppositeSide = "empire"
	} else if callerSide == "empire" {
		oppositeSide = "federation"
	}
	if oppositeSide != "" {
		teamPlayerCount := i.countConnectionsBySide(oppositeSide)
		totalPlayerCount := i.countTotalPlayers()
		var energyGain int
		if teamPlayerCount > 0 {
			energyGain = 250 / teamPlayerCount
		} else {
			energyGain = 500 / (totalPlayerCount + 1)
		}
		for _, base := range basePtrs {
			if base.Side == oppositeSide {
				base.ShipEnergy += energyGain
				const maxBaseEnergy = 50000
				if base.ShipEnergy > maxBaseEnergy {
					base.ShipEnergy = maxBaseEnergy
				}
			}
		}
	}

	// --- BASE PHASER DEFENSE ---
	for _, base := range basePtrs {
		targetsInRange := findEnemyShipsInRange(objectsCopy, base, galaxy, 4)
		for _, selectedTarget := range targetsInRange {
			totalPlayers := i.countTotalPlayers()
			if totalPlayers < 1 {
				totalPlayers = 1
			}
			energy := 200 / totalPlayers
			if energy < 1 {
				energy = 1
			}
			pendingDelayCalls = i.handlePhaserDefenseAttack(base, selectedTarget, energy, pendingDelayCalls)
		}
	}

	// --- PLANET PHASER DEFENSE ---
	var planetPtrs []*Object
	for _, obj := range objectsCopy {
		if obj.Galaxy == galaxy && obj.Type == "Planet" {
			planetPtrs = append(planetPtrs, obj)
		}
	}
	for _, planet := range planetPtrs {
		targetsInRange := findEnemyShipsInRange(objectsCopy, planet, galaxy, 2)
		for _, selectedTarget := range targetsInRange {
			energy := 50 + (30 * planet.Builds)
			pendingDelayCalls = i.handlePhaserDefenseAttack(planet, selectedTarget, energy, pendingDelayCalls)
		}
	}

	// --- ROMULAN TAUNT ---
	if len(romulanMoves) > 0 && RandomInt(100) < 25 {
		selectedRomulan := romulanMoves[RandomInt(len(romulanMoves))]
		leadins := []string{
			"Death to ",
			"Destruction to ",
			"I will crush ",
			"Prepare to die, ",
			"You have aroused my wrath, ",
			"I will reduce you to quarks, ",
		}
		adjectives := []string{
			"mindless ",
			"worthless ",
			"ignorant ",
			"idiotic ",
			"stupid ",
		}
		objects := []string{
			"mutant",
			"cretin",
			"toad",
			"worm",
			"parasite",
		}
		leadin := leadins[RandomInt(len(leadins))]
		adjective := adjectives[RandomInt(len(adjectives))]
		object := objects[RandomInt(len(objects))]
		targetChoice := RandomInt(4)
		var message string
		var targetSide string
		var targetPlayerName string
		var target string
		switch targetChoice {
		case 0:
			targetSide = "sub-Romulan "
			message = leadin + adjective + targetSide + object + "s"
			target = "all"
		case 1:
			targetSide = "human "
			message = leadin + adjective + targetSide + object + "s"
			target = "federation"
		case 2:
			targetSide = "klingon "
			message = leadin + adjective + targetSide + object + "s"
			target = "empire"
		case 3:
			var playersInRange []string
			for _, targetObj := range objectsCopy {
				if targetObj.Galaxy == galaxy && targetObj.Type == "Ship" && targetObj.Side != "romulan" {
					rangeX := AbsInt(targetObj.LocationX - selectedRomulan.LocationX)
					rangeY := AbsInt(targetObj.LocationY - selectedRomulan.LocationY)
					rangeDist := max(rangeX, rangeY)
					if rangeDist <= MaxRange {
						playersInRange = append(playersInRange, targetObj.Name)
					}
				}

			}
			if len(playersInRange) > 0 {
				targetPlayerName = playersInRange[RandomInt(len(playersInRange))]
				for _, targetObj := range objectsCopy {
					if targetObj.Name == targetPlayerName && targetObj.Galaxy == galaxy {
						if targetObj.Side == "federation" {
							targetSide = "human "
						} else if targetObj.Side == "empire" {
							targetSide = "klingon "
						} else {
							targetSide = "sub-Romulan "
						}
						break
					}
				}
				message = leadin + adjective + targetSide + object
				target = targetPlayerName
			} else {
				targetSide = "sub-Romulan "
				message = leadin + adjective + targetSide + object + "s"
				target = "all"
			}
		}
		if RandomInt(2) == 0 {
			message += "."
		} else {
			message += "!"
		}
		go i.broadcastRomulanTaunt(selectedRomulan.Name, target, message, galaxy)
	}

	// Process all pending delay calls after iteration is complete to prevent recursion
	for _, dc := range pendingDelayCalls {
		//		go i.delayPause(dc.conn, dc.numberMillisecond, dc.galaxy, dc.callerType, dc.callerSide)
		i.delayPause(dc.conn, dc.numberMillisecond, dc.galaxy, dc.callerType, dc.callerSide)
	}
}

// delayPause function - Romulans move, attack targets
func (i *Interpreter) delayPause(conn net.Conn, numberMillisecond int, galaxy uint16, callerType string, callerSide string) string {
	// Only human ships get delays - skip delay for robots (planets, bases, romulans)
	isRobot := callerType == "Planet" || callerType == "Base" || callerSide == "romulan"
	if DecwarMode && callerType == "Ship" && (callerSide == "federation" || callerSide == "empire") && !isRobot {
		time.Sleep(time.Duration(numberMillisecond) * time.Millisecond)
		// Always increment the stardate on timed moves
		if info, ok := i.connections.Load(conn); ok {
			connInfo := info.(ConnectionInfo)
			connInfo.Lock()
			shipname := connInfo.Shipname
			galaxy := connInfo.Galaxy
			connInfo.Unlock()
			if shipname != "" {
				ship := i.getShipByName(galaxy, shipname)
				if ship != nil {
					ship.StarDate++
				}
			}
		}
	}

	// Only human ships get delays
	//	i.robotsUnlocked(galaxy, callerSide)

	var destructionOutput strings.Builder

	// --- Phase 1: Snapshot objects and identify those needing destruction ---
	// Take RLock to safely snapshot the objects slice. With per-galaxy parallelism
	// another goroutine can shrink i.objects concurrently.
	i.spatialIndexMutex.RLock()
	delaySnapshot := make([]*Object, len(i.objects))
	copy(delaySnapshot, i.objects)
	i.spatialIndexMutex.RUnlock()

	// Collect objects that need to be destroyed (by pointer, not index)
	var objectsToDestroy []*Object

	for _, obj := range delaySnapshot {
		if obj.Galaxy != galaxy {
			continue
		}

		if obj.LifeSupportDamage > CriticalDamage {
			// If the ship is on life support decrement LifeSupportReserve
			obj.LifeSupportReserve--
		}
		// if obj.LifeSupportReserve < 0 or ShipEnergy <= 0, destroy the object.
		// Send notification messages only if not already sent (destructionFlag CAS),
		// but always perform the actual cleanup (remove object, reset connection).
		if obj.ShipEnergy <= 0 || obj.LifeSupportReserve <= 0 {
			// DestroyObject uses atomic.CompareAndSwapUint32 to guarantee exactly-once delivery.
			if i.DestroyObject(obj, galaxy) {
				// We won the CAS race: append the local (caller's terminal) destruction text.
				if obj.Type == "Ship" {
					displayName := obj.Name
					if strings.HasPrefix(displayName, "Romulan") {
						displayName = "Romulan"
					}
					destructionOutput.WriteString(fmt.Sprintf("%s RUNS OUT OF ENERGY!!\n\r%s DESTROYED!!\n\r", displayName, displayName))
				} else {
					destructionOutput.WriteString(fmt.Sprintf("%s has been destroyed at @%d-%d\n\r", obj.Name, obj.LocationX, obj.LocationY))
				}
			}

			if obj.Type == "Ship" {
				targetConn := i.getShipConnection(*obj)
				if targetConn != nil {
					if targetConnInfo, ok := i.connections.Load(targetConn); ok {
						ci := targetConnInfo.(ConnectionInfo)
						// Set destruction cooldown for this (IP, Port, Galaxy)
						i.setDestructionCooldownForConn(ci, obj.Galaxy)

						ci.Section = "pregame"
						ci.Shipname = ""
						ci.Ship = nil
						ci.BaudRate = 0
						i.connections.Store(targetConn, ci)
					}
				}
			}
			objectsToDestroy = append(objectsToDestroy, obj)
		}
	}

	// --- Phase 2: Remove destroyed objects under write lock ---
	// Find each object by pointer in the live slice and remove it.
	// Iterate backwards so removals don't shift indices of objects yet to process.
	if len(objectsToDestroy) > 0 {
		i.spatialIndexMutex.Lock()
		for _, condemned := range objectsToDestroy {
			for j := len(i.objects) - 1; j >= 0; j-- {
				if i.objects[j] == condemned {
					i.removeObjectByIndexLocked(j)
					break
				}
			}
		}
		i.spatialIndexMutex.Unlock()
		i.refreshShipPointers()
	}

	// Reincarnate any missing Romulans after destruction cleanup
	i.reincarnateRomulans(galaxy)

	return destructionOutput.String()
}

// reincarnateRomulans checks if the number of Romulans in the galaxy is below
// MaxRomulans (stored in the galaxy tracker) and spawns new ones at random
// collision-free locations, mirroring decwar behaviour.
func (i *Interpreter) reincarnateRomulans(galaxy uint16) {
	// Fetch galaxy parameters
	i.trackerMutex.Lock()
	tracker, exists := i.galaxyTracker[galaxy]
	i.trackerMutex.Unlock()
	if !exists || tracker.MaxRomulans <= 0 {
		return
	}
	maxRomulans := tracker.MaxRomulans
	decwarMode := tracker.DecwarMode
	galaxyMaxX := tracker.MaxSizeX
	galaxyMaxY := tracker.MaxSizeY
	if galaxyMaxX <= 0 {
		galaxyMaxX = MaxSizeX
	}
	if galaxyMaxY <= 0 {
		galaxyMaxY = MaxSizeY
	}

	// Count current Romulans and collect occupied positions
	i.spatialIndexMutex.RLock()
	currentCount := 0
	occupied := make(map[string]struct{})
	for _, obj := range i.objects {
		if obj.Galaxy != galaxy {
			continue
		}
		key := fmt.Sprintf("%d,%d", obj.LocationX, obj.LocationY)
		occupied[key] = struct{}{}
		if obj.Type == "Ship" && obj.Side == "romulan" {
			currentCount++
		}
	}
	i.spatialIndexMutex.RUnlock()

	if currentCount >= maxRomulans {
		return
	}

	// Determine effective max: in decwar mode only one Romulan is allowed
	effectiveMax := maxRomulans
	if decwarMode && effectiveMax > 1 {
		effectiveMax = 1
	}

	// Spawn missing Romulans one at a time
	spawned := false
	i.galaxiesMutex.RLock()
	gal := i.galaxies[galaxy]
	i.galaxiesMutex.RUnlock()
	galaxyRng := newSeededRand()
	if gal != nil {
		galaxyRng = gal.rng
	}
	for currentCount < effectiveMax {
		// Pick a collision-free random location
		var x, y int
		for attempts := 0; attempts < 1000; attempts++ {
			x = galaxyRng.Intn(galaxyMaxX) + 1
			y = galaxyRng.Intn(galaxyMaxY) + 1
			key := fmt.Sprintf("%d,%d", x, y)
			if _, taken := occupied[key]; !taken {
				occupied[key] = struct{}{}
				break
			}
			x, y = 0, 0
		}
		if x == 0 && y == 0 {
			// Could not find a free cell; give up for this pass
			break
		}

		// Choose a unique name
		var romName string
		if decwarMode {
			romName = "Romulan"
		} else {
			// Find the highest existing Romulan index and add 1
			i.spatialIndexMutex.RLock()
			maxIdx := currentCount
			for _, obj := range i.objects {
				if obj.Galaxy == galaxy && obj.Type == "Ship" && obj.Side == "romulan" {
					suffix := strings.TrimPrefix(obj.Name, "Romulan")
					if idx, err := strconv.Atoi(suffix); err == nil && idx >= maxIdx {
						maxIdx = idx + 1
					}
				}
			}
			i.spatialIndexMutex.RUnlock()
			romName = fmt.Sprintf("Romulan%d", maxIdx)
		}

		newRomulan := &Object{
			Galaxy:             galaxy,
			Type:               "Ship",
			LocationX:          x,
			LocationY:          y,
			Side:               "romulan",
			Name:               romName,
			Shields:            InitialShieldValue,
			Condition:          "Green",
			TorpedoTubes:       math.MaxInt,
			TorpedoTubeDamage:  0,
			PhasersDamage:      0,
			ComputerDamage:     0,
			LifeSupportDamage:  0,
			LifeSupportReserve: 5,
			RadioOnOff:         true,
			RadioDamage:        0,
			TractorOnOff:       false,
			TractorShip:        "",
			TractorDamage:      0,
			ShieldsUpDown:      true,
			ShipEnergy:         InitialShipEnergy,
			TotalShipDamage:    0,
			WarpEnginesDamage:  0,
			Builds:             0,
		}

		i.spatialIndexMutex.Lock()
		i.objects = append(i.objects, newRomulan)
		i.spatialIndexMutex.Unlock()

		log.Printf("[reincarnateRomulans] galaxy %d: spawned %s at (%d,%d) (was %d/%d)",
			galaxy, romName, x, y, currentCount, effectiveMax)

		spawned = true
		currentCount++
	}

	if spawned {
		// Rebuild spatial indexes once after all spawns
		i.rebuildSpatialIndexes()
		i.refreshShipPointers()
	}
}

// undockShipsFromDestroyedObject finds all ships docked at a destroyed base or planet
// and resets their condition to Green or Red (removing the Docked status).
// Ships are considered docked at an object if they are adjacent (within 1 sector) and
// their Condition contains "Docked".
func (i *Interpreter) undockShipsFromDestroyedObject(obj *Object, galaxy uint16) {
	if obj.Type != "Base" && obj.Type != "Planet" {
		return
	}
	for idx := range i.objects {
		ship := i.objects[idx]
		if ship.Type != "Ship" || ship.Galaxy != galaxy {
			continue
		}
		if !strings.Contains(strings.ToLower(ship.Condition), "docked") {
			continue
		}
		// Check if this ship is adjacent to (within 1 sector of) the destroyed object
		dx := ship.LocationX - obj.LocationX
		dy := ship.LocationY - obj.LocationY
		if dx < -1 || dx > 1 || dy < -1 || dy > 1 {
			continue
		}
		// Undock: preserve Red alert if present, otherwise set Green
		if strings.Contains(ship.Condition, "Red") {
			i.objects[idx].Condition = "Red"
		} else {
			i.objects[idx].Condition = "Green"
		}
		// Notify the player that their docked base/planet was destroyed
		shipName := ship.Name
		i.connections.Range(func(key, value interface{}) bool {
			conn := key.(net.Conn)
			connInfo := value.(ConnectionInfo)
			if connInfo.Galaxy != galaxy || connInfo.Ship == nil || connInfo.Ship.Name != shipName {
				return true
			}
			if writerRaw, ok := i.writers.Load(conn); ok {
				writer := writerRaw.(*bufio.Writer)
				displayName := obj.Name
				if strings.HasPrefix(displayName, "Base") {
					displayName = "Base"
				} else if strings.HasPrefix(displayName, "Planet") {
					displayName = "Planet"
				}
				i.writeBaudf(conn, writer, "%s %s DESTROYED!! You are no longer docked.\r\n", obj.Side, displayName)
			}
			return false
		})
	}
}

// broadcastDestructionEvent broadcasts destruction messages using the event messaging system.
// Callers must have already won the atomic.CompareAndSwapUint32 race on obj.destructionFlag
// before invoking this function, so it never needs to check the flag itself.
func (i *Interpreter) broadcastDestructionEvent(obj *Object, galaxy uint16) {
	// If a base or planet was destroyed, undock any ships that were docked there
	if obj.Type == "Base" || obj.Type == "Planet" {
		i.undockShipsFromDestroyedObject(obj, galaxy)
	}
	// Find all ships within scanning range of the destroyed object
	ships := i.getObjectsByType(galaxy, "Ship")
	if ships == nil {
		return
	}

	for _, ship := range ships {
		// Skip the destroyed object itself
		if ship.Name == obj.Name {
			continue
		}

		// Check if ship is within scanning range of the destroyed object
		if !((ship.LocationX >= obj.LocationX-(DefScanRange/2) && ship.LocationX <= obj.LocationX+(DefScanRange/2)) &&
			(ship.LocationY >= obj.LocationY-(DefScanRange/2) && ship.LocationY <= obj.LocationY+(DefScanRange/2))) {
			continue // Skip ships outside scanning range
		}

		// Find the connection for this ship
		i.connections.Range(func(key, value interface{}) bool {
			conn := key.(net.Conn)
			connInfo := value.(ConnectionInfo)
			if connInfo.Galaxy != galaxy {
				return true
			}
			if connInfo.Ship == nil || connInfo.Ship.Name != ship.Name {
				return true
			}
			// Only send to active ships
			if connInfo.Section != "gowars" {
				return true
			}
			// Only send if the receiving ship's radio is ON
			if !connInfo.Ship.RadioOnOff {
				return true
			}

			var message string
			// Get display name - strip numbered suffix from Romulans
			displayName := obj.Name
			if strings.HasPrefix(displayName, "Romulan") {
				displayName = "Romulan"
			}
			if strings.HasPrefix(displayName, "Planet") {
				displayName = "Planet"
			}
			if strings.HasPrefix(displayName, "Base") {
				displayName = "Base"
			}
			if strings.HasPrefix(displayName, "Planet") {
				displayName = "Planet"
			}

			if obj.Type == "Ship" {
				if obj.ShipEnergy <= 0 {
					message = fmt.Sprintf("%s RUNS OUT OF ENERGY!!\n\r", displayName)
				}
				if obj.LifeSupportReserve <= 0 || obj.ShipEnergy <= 0 {
					message += fmt.Sprintf("%s DESTROYED!!\n\r", displayName)
				}
			} else {
				message = fmt.Sprintf("%s %s DESTROYED!!\n\r", obj.Side, displayName)
			}

			if message != "" {
				if writerRaw, ok := i.writers.Load(conn); ok {
					writer := writerRaw.(*bufio.Writer)
					i.writeBaudf(conn, writer, "%s", message)

					// Re-draw the player's prompt
					prompt := i.getPrompt(conn)
					if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
						mutex := mutexRaw.(*sync.Mutex)
						mutex.Lock()
						writer.WriteString(prompt)
						writer.Flush()
						mutex.Unlock()
					}
				}
			}
			return false // Stop once we find the right connection for this ship
		})
	}
}

// DestroyObject is the single authoritative function for emitting destruction
// messages about obj in galaxy.  It uses atomic.CompareAndSwapUint32 on
// obj.destructionFlag to guarantee the broadcast fires exactly once, even when
// multiple goroutines (delayPause, DoDamage, broadcastDestructionEvent callers)
// race to destroy the same object simultaneously.
//
// Returns true if this call won the CAS race and emitted the messages, or false
// if another goroutine already did so (caller should skip further notification).
func (i *Interpreter) DestroyObject(obj *Object, galaxy uint16) bool {
	// CAS: only the goroutine that transitions 0->1 broadcasts.
	if !atomic.CompareAndSwapUint32(&obj.destructionFlag, 0, 1) {
		return false // Another goroutine already handled destruction messaging.
	}
	// Won the race -- emit all destruction messages exactly once.
	i.broadcastDestructionEvent(obj, galaxy)
	return true
}

// gameender goroutine - checks for end of game conditions every second
func (i *Interpreter) gameender() {
	ticker := time.NewTicker(1 * time.Second)
	defer ticker.Stop()

	for {
		select {
		case <-ticker.C:
			// Check all active galaxies for end game conditions
			activeGalaxies := make(map[uint16]bool)

			// Find all active galaxies by checking connections
			i.connections.Range(func(key, value interface{}) bool {
				connInfo := value.(ConnectionInfo)
				if connInfo.Galaxy > 0 && connInfo.Section == "gowars" {
					activeGalaxies[connInfo.Galaxy] = true
				}
				return true
			})

			// Check each active galaxy for end game conditions
			for galaxy := range activeGalaxies {
				i.checkEndGameConditions(galaxy)
			}
		case <-i.shutdown:
			log.Printf("Game ender shutting down")
			return
		}
	}
}

// checkEndGameConditions checks if the war is over in the specified galaxy
func (i *Interpreter) checkEndGameConditions(galaxy uint16) {
	// After removing all dead ships, count bases and planets for each side in this galaxy
	fedBases := 0
	empBases := 0
	fedPlanets := 0
	empPlanets := 0

	bases := i.getObjectsByType(galaxy, "Base")
	if bases != nil {
		for _, obj := range bases {
			if obj.Side == "federation" {
				fedBases++
			} else if obj.Side == "empire" {
				empBases++
			}
		}
	}

	planets := i.getObjectsByType(galaxy, "Planet")
	if planets != nil {
		for _, obj := range planets {
			if obj.Side == "federation" {
				fedPlanets++
			} else if obj.Side == "empire" {
				empPlanets++
			}
		}
	}

	// New end game conditions: a side loses if it has no bases AND no planets
	if (fedBases <= 0 && fedPlanets <= 0) && (empBases <= 0 && empPlanets <= 0) {
		i.broadcastRomulanTaunt("SYSTEM", "all", "THE WAR IS OVER!!", galaxy)
		i.broadcastRomulanTaunt("SYSTEM", "all", "The entire known galaxy has been depopulated.\r\nBOTH sides lose!!", galaxy)
	} else if fedBases <= 0 && fedPlanets <= 0 {
		i.broadcastRomulanTaunt("SYSTEM", "all", "THE WAR IS OVER!!", galaxy)
		i.broadcastRomulanTaunt("SYSTEM", "all", "The Klingon Empire is VICTORIOUS!!", galaxy)
		i.broadcastRomulanTaunt("SYSTEM", "federation", "Please proceed to the nearest Klingon slave planet.", galaxy)
		i.broadcastRomulanTaunt("SYSTEM", "empire", "The Empire salutes you.  Begin slave operations immediately.", galaxy)
	} else if empBases <= 0 && empPlanets <= 0 {
		i.broadcastRomulanTaunt("SYSTEM", "all", "THE WAR IS OVER!!", galaxy)
		i.broadcastRomulanTaunt("SYSTEM", "all", "The Federation has successfully repelled the Klingon hordes!", galaxy)
		i.broadcastRomulanTaunt("SYSTEM", "federation", "Congratulations.  Freedom again reigns the galaxy.", galaxy)
		i.broadcastRomulanTaunt("SYSTEM", "empire", "The Empire has fallen.  Initiate self-destruction procedure.", galaxy)
	}

	// Move all players in this galaxy back to pregame after the war ends
	if (fedBases <= 0 && fedPlanets <= 0) || (empBases <= 0 && empPlanets <= 0) {
		i.connections.Range(func(key, value interface{}) bool {
			conn := key.(net.Conn)
			info := value.(ConnectionInfo)
			if info.Galaxy == galaxy && info.Section == "gowars" {
				if info.Ship != nil {
					info.Ship.EnteredTime = nil
				}
				info.Section = "pregame"
				info.Shipname = ""
				info.Ship = nil
				info.Galaxy = 0
				info.Prompt = ""
				info.BaudRate = 0
				i.connections.Store(conn, info)
				if writerRaw, ok := i.writers.Load(conn); ok {
					writer := writerRaw.(*bufio.Writer)
					if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
						mutex := mutexRaw.(*sync.Mutex)
						mutex.Lock()
						fmt.Fprintf(writer, "\r\nThe war is over! You have been returned to pregame.\r\n")
						writer.Flush()
						mutex.Unlock()
					}
				}
			}
			return true
		})

		// Reinitialize the galaxy for a new game.
		log.Printf("Reinitializing galaxy %d for a new game.", galaxy)

		i.spatialIndexMutex.Lock()
		var remainingObjects []*Object
		for _, obj := range i.objects {
			if obj.Galaxy != galaxy {
				remainingObjects = append(remainingObjects, obj)
			}
		}
		i.objects = remainingObjects
		i.spatialIndexMutex.Unlock()

		// Re-populate the galaxy with a new set of objects atomically.
		params := getDefaultGalaxyParams()
		i.resetAndReinitializeGalaxy(galaxy, params)
		log.Printf("Galaxy %d reinitialized.", galaxy)
	}
}

// Perform delay calc and pause for move (different from decwar)
// Calc pause based on slwest (from decwar):
//	slwest = 1 (<=1200)
//	slwest = 2 (=1200?)
//	slwest = 3 (>1200)
//	slwest = 0 (= 0)
// decwar: Simple move charge: (slwest×1000)+1000
//         if going > 4 sectors: rand(4000)/30 (add or not?)

// calculateDlypse calculates the delay/pause value for move and impulse commands (among others)
func calculateDlypse(baudRate int, startX, startY, targetX, targetY int) int {
	var dlypse int
	if baudRate < 1200 && baudRate > 0 {
		dlypse = 1
	} else if baudRate == 1200 {
		dlypse = 2
	} else if baudRate > 1200 {
		dlypse = 3
	} else { // must be 0
		dlypse = 0
	}
	dlypse = (dlypse * 1000) + 1000

	// overheating charge for moves > 4 sectors
	if AbsInt(startX-targetX) > 4 || AbsInt(startY-targetY) > 4 {
		rnd := RandomInt(4000)
		dlypse = dlypse + (rnd / 30)
	}
	return dlypse
}

func AbsInt(x int) int {
	if x < 0 {
		return -x
	}
	return x
}

// SelectObjectsWithCenters handles object selection using centers logic or DecwarMode.
func (i *Interpreter) SelectObjectsWithCenters(
	conn net.Conn,
	objects []*Object,
	centers []struct{ X, Y int },
	radius int,
	filter func(obj Object) bool,
	radiusSpecified bool,
) []*Object {
	if !DecwarMode {
		// Use spatial indexing for optimized selection
		var selected []*Object

		// Get galaxy from connection
		galaxy := uint16(0)
		if info, ok := i.connections.Load(conn); ok {
			galaxy = info.(ConnectionInfo).Galaxy
		}

		// For each center, check all coordinates within radius
		seenObjects := make(map[*Object]struct{})
		for _, center := range centers {
			for x := center.X - radius; x <= center.X+radius; x++ {
				for y := center.Y - radius; y <= center.Y+radius; y++ {
					obj := i.getObjectAtLocation(galaxy, x, y)
					if obj != nil && filter(*obj) {
						if _, seen := seenObjects[obj]; !seen {
							selected = append(selected, obj)
							seenObjects[obj] = struct{}{}
						}
					}
				}
			}
		}
		return selected
	} else {
		// Pass radiusSpecified to stub
		return i.SelectObjectsIntelligentStub(conn, objects, centers, radius, filter, radiusSpecified)
	}
}

// DecwarMode: Set SeenByFed/SeenByEmp for objects within range of friendly centers
func (i *Interpreter) SelectObjectsIntelligentStub(
	conn net.Conn,
	objects []*Object,
	centers []struct{ X, Y int },
	radius int,
	filter func(obj Object) bool,
	radiusSpecified bool,
) []*Object {

	var galaxy uint16

	// Get galaxy
	info, ok := i.connections.Load(conn)
	if ok {
		galaxy = info.(ConnectionInfo).Galaxy
	}

	// Determine "my side" from the centers (assume all centers are friendly)
	mySide := ""
	for _, center := range centers {
		obj := i.getObjectAtLocation(galaxy, center.X, center.Y)
		if obj != nil && (obj.Type == "Ship" || obj.Type == "Base") {
			mySide = obj.Side
			break
		}
	}

	// First, set SeenByFed/SeenByEmp for objects in range of any center using spatial indexing
	for _, center := range centers {
		for x := center.X - radius; x <= center.X+radius; x++ {
			for y := center.Y - radius; y <= center.Y+radius; y++ {
				obj := i.getObjectAtLocation(galaxy, x, y)
				if obj != nil && filter(*obj) {
					if mySide == "federation" {
						obj.SeenByFed = true
					} else if mySide == "empire" {
						obj.SeenByEmp = true
					}
				}
			}
		}
	}

	// Helper function to determine if filter is type-specific for optimization
	determineOptimalStrategy := func() ([]string, bool) {
		commonTypes := []string{"Ship", "Base", "Planet", "Star", "Black Hole", "Romulan"}
		acceptedTypes := []string{}

		// Test the filter against minimal sample objects for each type
		for _, objType := range commonTypes {
			// Create a basic sample object for this type
			sample := Object{
				Galaxy: galaxy,
				Type:   objType,
				Side:   "neutral", // Use neutral as a safe default for testing
			}

			// Test if this type might be accepted by the filter
			// Use defensive programming in case filter has side effects
			accepted := false
			func() {
				defer func() {
					if recover() != nil {
						// If filter panics, consider this type not accepted
						accepted = false
					}
				}()
				accepted = filter(sample)
			}()

			if accepted {
				acceptedTypes = append(acceptedTypes, objType)
			}
		}

		// Use type-specific optimization if we can limit to 3 or fewer types
		// This provides a good balance between optimization benefit and complexity
		canOptimize := len(acceptedTypes) > 0 && len(acceptedTypes) <= 3
		return acceptedTypes, canOptimize
	}

	acceptedTypes, useTypeOptimization := determineOptimalStrategy()
	var selected []*Object

	// Choose optimization strategy based on filter analysis
	if useTypeOptimization {
		// Use objectsByType for efficient type-specific filtering
		for _, objType := range acceptedTypes {
			typeObjects := i.getObjectsByType(galaxy, objType)
			for _, objPtr := range typeObjects {
				if objPtr == nil {
					continue
				}
				obj := *objPtr

				// Still need to apply the full filter as our analysis was just a heuristic
				if !filter(obj) {
					continue
				}

				// Check if object was marked as seen by appropriate side
				if (mySide == "federation" && obj.SeenByFed) || (mySide == "empire" && obj.SeenByEmp) {
					selected = append(selected, objPtr)
				}
			}
		}
	} else {
		// Use traditional iteration when type-specific optimization isn't beneficial
		for _, objPtr := range i.objects {
			obj := *objPtr
			// Early galaxy check to avoid processing irrelevant objects
			if obj.Galaxy != galaxy {
				continue
			}

			if !filter(obj) {
				continue
			}

			if (mySide == "federation" && obj.SeenByFed) || (mySide == "empire" && obj.SeenByEmp) {
				selected = append(selected, objPtr)
			}
		}
	}

	// If radiusSpecified, filter selected to only those within range of my ship
	if radiusSpecified {
		myShipX, myShipY := -1, -1
		ships := i.getObjectsByType(galaxy, "Ship")
		for _, ship := range ships {
			if ship.Side == mySide {
				myShipX = ship.LocationX
				myShipY = ship.LocationY
				break
			}
		}
		if myShipX != -1 && myShipY != -1 {
			filtered := selected[:0]
			for _, objPtr := range selected {
				dx := objPtr.LocationX - myShipX
				dy := objPtr.LocationY - myShipY
				if AbsInt(dx) <= radius && AbsInt(dy) <= radius {
					filtered = append(filtered, objPtr)
				}
			}
			selected = filtered
		}
	}

	return selected
}

// resolveScanAbbrev resolves a partial scan argument against a list of valid options.
// Numbers are accepted as-is; otherwise the input must uniquely prefix-match one option.
func resolveScanAbbrev(input string, options []string) (string, bool) {
	input = strings.ToLower(input)
	var matches []string
	for _, opt := range options {
		if strings.HasPrefix(opt, input) {
			matches = append(matches, opt)
		}
	}
	if len(matches) == 1 {
		return matches[0], true
	}
	if _, err := strconv.Atoi(input); err == nil {
		return input, true
	}
	return "", false
}

// parseScanDimensions parses optional size arguments (1 or 2 numbers after the
// direction keyword) and returns (rows, cols, errorMsg). An empty errorMsg means
// success.  tempArgs[0] is the direction keyword itself, so sizes start at index 1.
func parseScanDimensions(tempArgs []string, rangeDefault int) (int, int, string) {
	rows, cols := rangeDefault, rangeDefault
	if len(tempArgs) == 2 {
		v, err := strconv.Atoi(tempArgs[1])
		if err != nil {
			return 0, 0, "Error:"
		}
		if v <= 1 || v > rows/2 {
			return 0, 0, "Error: Invalid size."
		}
		rows, cols = v*2, v*2
	}
	if len(tempArgs) == 3 {
		v1, err := strconv.Atoi(tempArgs[1])
		if err != nil {
			return 0, 0, "Error:"
		}
		if v1 <= 1 || v1 > rows/2 {
			return 0, 0, "Error: Invalid size."
		}
		rows = v1 * 2

		v2, err := strconv.Atoi(tempArgs[2])
		if err != nil {
			return 0, 0, "Error:"
		}
		if v2 <= 1 || v2 > cols/2 {
			return 0, 0, "Error: Invalid size."
		}
		cols = v2 * 2
	}
	return rows, cols, ""
}

// computeDirectionalScanBounds returns (startX, startY, endX, endY) for the
// four cardinal scan directions based on the ship position and desired rows/cols.
func computeDirectionalScanBounds(direction string, shipX, shipY, rows, cols int) (int, int, int, int) {
	switch direction {
	case "up":
		return shipX, shipY - cols/2, shipX + rows/2, shipY + cols/2
	case "down":
		return shipX - rows/2, shipY - cols/2, shipX, shipY + cols/2
	case "left":
		return shipX - rows/2, shipY - cols/2, shipX + rows/2, shipY
	case "right":
		return shipX - rows/2, shipY, shipX + rows/2, shipY + cols/2
	default:
		return shipX - rows/2, shipY - cols/2, shipX + rows/2, shipY + cols/2
	}
}

func (i *Interpreter) handleScanCtx(ctx context.Context, rangeDefault int, args []string, conn net.Conn) string {
	if info, ok := i.connections.Load(conn); !ok || info.(ConnectionInfo).Shipname == "" {
		return "Error: you must be in GOWARS with a shipname to use scan"
	}

	scanFirstOpts := []string{"up", "down", "right", "left", "corner", "warn"}
	scanOtherOpts := []string{"warn"}

	resolvedArgs := make([]string, len(args))
	for idx, arg := range args {
		options := scanOtherOpts
		if idx == 0 {
			options = scanFirstOpts
		}
		resolved, ok := resolveScanAbbrev(arg, options)
		if !ok {
			return fmt.Sprintf("Error: parameter %d ('%s') is invalid.", idx+1, arg)
		}
		resolvedArgs[idx] = resolved
	}

	// Separate "warn" flag from positional arguments
	rangeWarn := false
	var tempArgs []string
	for _, arg := range resolvedArgs {
		if arg == "warn" {
			rangeWarn = true
		} else {
			tempArgs = append(tempArgs, arg)
		}
	}

	// Default chart range
	shipX, shipY, _ := i.getShipLocation(conn)

	// Get scan mode for this connection
	scanShort := false
	if info, ok := i.connections.Load(conn); ok {
		scanShort = info.(ConnectionInfo).Scan == "short"
	}

	// Compute default scan bounds centred on the ship
	defaultBounds := func() (int, int, int, int) {
		if scanShort {
			return shipX - rangeDefault/2, shipY - rangeDefault/2 + 1,
				shipX + rangeDefault/2, shipY + rangeDefault/2 - 1
		}
		return shipX - rangeDefault/2, shipY - rangeDefault/2,
			shipX + rangeDefault/2, shipY + rangeDefault/2
	}

	// ** Default output - no positional args (optionally just "warn") **
	if len(tempArgs) == 0 {
		startX, startY, endX, endY := defaultBounds()
		return i.outputScan(conn, scanShort, rangeWarn, startX, startY, endX, endY)
	}

	// ** Directional scans: up / down / left / right **
	direction := tempArgs[0]
	if direction == "up" || direction == "down" || direction == "left" || direction == "right" {
		shipX, shipY, ok := i.getShipLocation(conn)
		if !ok {
			return "Error: Unable to determine ship location."
		}
		rows, cols, errMsg := parseScanDimensions(tempArgs, rangeDefault)
		if errMsg != "" {
			return errMsg
		}
		startX, startY, endX, endY := computeDirectionalScanBounds(direction, shipX, shipY, rows, cols)
		return i.outputScan(conn, scanShort, rangeWarn, startX, startY, endX, endY)
	}

	// ** Corner parameter support **
	if direction == "corner" {
		if len(args) >= 3 {
			p3, ok2 := resolveScanAbbrev(args[2], scanOtherOpts)
			if !ok2 {
				return "Error: Second parameter must be warn or a number."
			}
			p2, ok2 := resolveScanAbbrev(args[1], scanOtherOpts)
			if !ok2 {
				return "Error: First parameter must be a number."
			}

			j, err := strconv.Atoi(p2)
			if err != nil {
				return "Error: First parameter must be a number."
			}
			if AbsInt(j) > rangeDefault/2 {
				return "Error: Invalid size."
			}
			k, err := strconv.Atoi(p3)
			if err != nil {
				return "Error:"
			}
			if AbsInt(k) > rangeDefault/2 {
				return "Error: Invalid size."
			}

			// Figure out the range depending on requested values
			var startX, startY, endX, endY int
			if j > 0 {
				if k > 0 {
					startX, startY = shipX, shipY
					endX, endY = shipX+j, shipY+k
				} else {
					startX, startY = shipX, shipY+k
					endX, endY = shipX+j, shipY
				}
			} else {
				if k < 0 {
					startX, startY = shipX+j, shipY+k
					endX, endY = shipX, shipY
				} else {
					startX, startY = shipX+j, shipY
					endX, endY = shipX, shipY+k
				}
			}
			return i.outputScan(conn, scanShort, rangeWarn, startX, startY, endX, endY)
		}
		return "Scan Corner requires two parameters, with an optional warning."
	}

	// ** Numeric range: 1 or 2 numbers, optionally with warn **
	// At this point tempArgs[0] should be a number (direction keywords already handled).
	rangeX, err := strconv.Atoi(tempArgs[0])
	if err != nil {
		return "Error: invalid entry"
	}

	rangeY := rangeX // default: symmetric range
	if len(tempArgs) >= 2 {
		rangeY, err = strconv.Atoi(tempArgs[1])
		if err != nil {
			return "Error: invalid entry"
		}
	}

	if rangeX < 1 || rangeX > 10 || rangeY < 1 || rangeY > 10 {
		return "Error: range must be a number between 1 and 10"
	}

	shipX, shipY, ok := i.getShipLocation(conn)
	if !ok {
		return "Error: Unable to determine ship location."
	}

	startX := shipX - rangeX
	startY := shipY - rangeY
	endX := shipX + rangeX
	endY := shipY + rangeY

	// Use context-aware version when warn is set with two range params
	if len(tempArgs) >= 2 && rangeWarn {
		return i.outputScanCtx(ctx, conn, scanShort, rangeWarn, startX, startY, endX, endY)
	}
	return i.outputScan(conn, scanShort, rangeWarn, startX, startY, endX, endY)
}

// outputScan handles the default scan logic.  Output for a x range and y range, within a galaxy
func (i *Interpreter) outputScan(conn net.Conn, scanShort bool, rangeWarn bool, xLow, yLow, xHigh, yHigh int) string {
	return i.outputScanCtx(context.Background(), conn, scanShort, rangeWarn, xLow, yLow, xHigh, yHigh)
}

func (i *Interpreter) outputScanCtx(ctx context.Context, conn net.Conn, scanShort bool, rangeWarn bool, xLow, yLow, xHigh, yHigh int) string {
	return i.outputScanCtxWithGalaxy(ctx, conn, 0, scanShort, rangeWarn, xLow, yLow, xHigh, yHigh)
}

func (i *Interpreter) outputScanCtxWithGalaxy(ctx context.Context, conn net.Conn, galaxy uint16, scanShort bool, rangeWarn bool, xLow, yLow, xHigh, yHigh int) string {

	// If galaxy is 0, try to get it from connection
	if galaxy == 0 && conn != nil {
		info, ok := i.connections.Load(conn)
		if ok {
			galaxy = info.(ConnectionInfo).Galaxy
		}
	}

	// Get actual galaxy bounds
	actualMaxSizeX := MaxSizeX
	actualMaxSizeY := MaxSizeY
	i.trackerMutex.Lock()
	if tracker, exists := i.galaxyTracker[galaxy]; exists {
		if tracker.MaxSizeX > 0 {
			actualMaxSizeX = tracker.MaxSizeX
		}
		if tracker.MaxSizeY > 0 {
			actualMaxSizeY = tracker.MaxSizeY
		}
	}
	i.trackerMutex.Unlock()

	// Clip range
	if xLow <= BoardStart {
		xLow = BoardStart
	}
	if xHigh > actualMaxSizeX {
		xHigh = actualMaxSizeX
	}
	if yLow <= BoardStart {
		yLow = BoardStart
	}
	if yHigh > actualMaxSizeY {
		yHigh = actualMaxSizeY
	}

	// Get the side my ship is on before filtering out "warn"
	side, sideOk := i.getShipSide(conn)
	_ = sideOk

	// Build header
	var header strings.Builder

	if scanShort && xLow == BoardStart {
		header.WriteString("  ")
	} else {
		if scanShort && xHigh == actualMaxSizeX {
			header.WriteString("  ")
		} else {
			header.WriteString("   ")
		}
	}

	for c := yLow; c <= yHigh; c++ {
		if scanShort {
			if (c-yLow)%3 == 0 {
				header.WriteString(fmt.Sprintf("%2d ", c))
			}
		} else {
			if c%2 == yLow%2 {
				header.WriteString(fmt.Sprintf("%2d", c))
			} else {
				header.WriteString("  ")
			}
		}
	}
	header.WriteString("\r\n")

	// Fix so it looks like decwar, but respect actual galaxy height
	if scanShort && yHigh < (actualMaxSizeY-1) {
		//		yLow = yLow - 1
		yHigh = yHigh + 1
	}
	if scanShort && yLow < BoardStart+1 {
		yLow = BoardStart
	}

	// Build chart
	var chart strings.Builder
	chart.WriteString(header.String())
	for r := xHigh; r >= xLow; r-- {
		// Check for context cancellation during chart building
		select {
		case <-ctx.Done():
			return "[Output interrupted]"
		default:
		}
		xLabel := r

		if scanShort && yHigh == actualMaxSizeY {
			chart.WriteString(fmt.Sprintf("%2d ", xLabel))
		} else {
			chart.WriteString(fmt.Sprintf("%2d ", xLabel))
		}

		for c := yLow; c <= yHigh; c++ {
			// Check for context cancellation during column processing
			select {
			case <-ctx.Done():
				return "[Output interrupted]"
			default:
			}
			cell := " ."
			if scanShort {
				cell = "."
			}
			if rangeWarn == true {
				if i.withinRange(r, c, 2, "Planet", side, galaxy) || i.withinRange(r, c, 4, "Base", side, galaxy) {
					if scanShort {
						cell = "!"
					} else {
						cell = " !"
					}
				}
			}

			// Direct coordinate lookup instead of scanning all objects
			obj := i.getObjectAtLocation(galaxy, r, c)
			if obj != nil {
				switch obj.Type {
				case "Ship":
					if obj.Side == "romulan" {
						if scanShort {
							cell = "~"
						} else {
							cell = "~~"
						}
					} else {
						if len(obj.Name) > 0 {
							if scanShort {
								cell = strings.ToUpper(obj.Name[:1])
							} else {
								cell = fmt.Sprintf(" %s", strings.ToUpper(obj.Name[:1]))
							}
						} else {
							if scanShort {
								cell = "?"
							} else {
								cell = " ?"
							}
						}
					}
				case "Base":
					if obj.Side == "federation" {
						if scanShort {
							cell = "["
						} else {
							cell = "[]"
						}
					} else if obj.Side == "empire" {
						if scanShort {
							cell = "("
						} else {
							cell = "()"
						}
					}
				case "Planet":
					switch obj.Side {
					case "neutral":
						if scanShort {
							cell = "@"
						} else {
							cell = " @"
						}
					case "federation":
						if scanShort {
							cell = "+"
						} else {
							cell = "+@"
						}
					case "empire":
						if scanShort {
							cell = "-"
						} else {
							cell = "-@"
						}
					}
				case "Star":
					if scanShort {
						cell = "*"
					} else {
						cell = " *"
					}
				case "Black Hole":
					if scanShort {
						cell = " "
					} else {
						cell = "  "
					}
				default:
					if scanShort {
						cell = "?"
					} else {
						cell = " ?"
					}
				}
			}

			chart.WriteString(cell)
		}
		chart.WriteString(fmt.Sprintf(" %2d\r\n", xLabel))
	}
	chart.WriteString(header.String())
	return chart.String()
}

// Object represents an entry in the objects database
type Object struct {
	Galaxy               uint16
	Type                 string
	LocationX            int
	LocationY            int
	Side                 string
	Name                 string // Added for ships to store shipname
	Shields              int    // Shields value for the object (0 for non-ships by default)
	ShieldsDamage        int
	WarpEngines          int
	WarpEnginesDamage    int
	ImpulseEnginesDamage int
	TorpedoTubes         int
	TorpedoTubeDamage    int
	PhasersDamage        int
	ComputerDamage       int
	LifeSupportDamage    int
	LifeSupportReserve   int
	RadioOnOff           bool
	RadioDamage          int
	TractorOnOff         bool
	TractorShip          string
	TractorDamage        int
	StarDate             int
	Condition            string
	ShipEnergy           int  // Ship energy value for ships (default 5000)
	SeenByFed            bool // Has this object been seen by Federation?
	SeenByEmp            bool // Has this object been seen by Empire?
	ShieldsUpDown        bool
	TotalShipDamage      int        // Total ship damage for this object
	Builds               int        // Number of builds for this object, defaults to 0
	EnteredTime          *time.Time // Time when ship entered the game, nil when not in game
	destructionFlag      uint32     // Atomic flag: 0 = not sent, 1 = sent. Use atomic.CompareAndSwapUint32.
}

// ConnectionInfo holds data about a connected client
type ConnectionInfo struct {
	sync.Mutex
	IP              string
	Port            string
	ConnTime        time.Time
	LastActivity    time.Time      // Tracks last activity for timeout
	Section         string         // "pregame" or "gowars"
	Shipname        string         // Ship name if activated, empty if not
	Ship            *Object        // Direct pointer to player's ship object, nil if not activated
	Galaxy          uint16         // Galaxy number (0-65535)
	OutputState     string         // "long", "medium", or "short" for output formatting
	Prompt          string         // Custom prompt string, empty for default
	OCdef           string         // "relative", "absolute", or "both" for output formatting
	Scan            string         // "long" or "short" for scan output
	CommandQueue    chan *GameTask // Per-ship command queue for individual command processing
	ICdef           string         // "relative" or "absolute" for icdef output
	Name            string         // User-settable name via set name
	RangeWarn       bool           // Whether to show range warnings
	CommandHistory  []string       // Stores entered commands for history navigation
	HistoryIndex    int            // Tracks current position in history for navigation
	BaudRate        int            // Baud rate for output simulation (300, 1200, 2400, 9600)
	TotalShipDamage int
	AdminMode       bool         // Whether this connection is in admin mode
	PreferredSide   string       // Tracks which side player initially chose (federation/empire)
	CmdRateLimiter  *TokenBucket // Per-connection command-rate limiter
}

// ---------------------------------------------------------------------------
// Rate-limiting primitives
// ---------------------------------------------------------------------------

// TokenBucket implements a simple token-bucket rate limiter.
type TokenBucket struct {
	mu         sync.Mutex
	tokens     float64
	maxTokens  float64
	refillRate float64 // tokens per second
	lastRefill time.Time
}

// NewTokenBucket creates a TokenBucket with the given burst size and per-second refill rate.
func NewTokenBucket(max float64, perSecond float64) *TokenBucket {
	return &TokenBucket{
		tokens:     max,
		maxTokens:  max,
		refillRate: perSecond,
		lastRefill: time.Now(),
	}
}

// Take consumes one token and returns true if the request is allowed.
func (b *TokenBucket) Take() bool {
	b.mu.Lock()
	defer b.mu.Unlock()

	now := time.Now()
	elapsed := now.Sub(b.lastRefill).Seconds()
	b.tokens = math.Min(b.maxTokens, b.tokens+elapsed*b.refillRate)
	b.lastRefill = now

	if b.tokens < 1.0 {
		return false
	}
	b.tokens--
	return true
}

// Connection throttling constants.
const (
	MaxConnsPerIP    = 3           // max simultaneous connections from one IP
	ConnRatePeriod   = time.Minute // sliding-window duration
	MaxNewConnsPerIP = 10          // max NEW connections per IP per window
)

// IPTracker limits per-IP connection counts and new-connection rates.
type IPTracker struct {
	mu           sync.Mutex
	activeCounts map[string]int
	newConns     map[string][]time.Time
}

// NewIPTracker constructs an initialised IPTracker.
func NewIPTracker() *IPTracker {
	return &IPTracker{
		activeCounts: make(map[string]int),
		newConns:     make(map[string][]time.Time),
	}
}

// Allow returns true when the connection from ip should be accepted.
func (t *IPTracker) Allow(ip string) bool {
	t.mu.Lock()
	defer t.mu.Unlock()

	now := time.Now()
	cutoff := now.Add(-ConnRatePeriod)

	// Prune timestamps outside the sliding window.
	recent := t.newConns[ip][:0]
	for _, ts := range t.newConns[ip] {
		if ts.After(cutoff) {
			recent = append(recent, ts)
		}
	}
	t.newConns[ip] = recent

	if t.activeCounts[ip] >= MaxConnsPerIP {
		return false
	}
	if len(recent) >= MaxNewConnsPerIP {
		return false
	}

	t.newConns[ip] = append(t.newConns[ip], now)
	t.activeCounts[ip]++
	return true
}

// Release decrements the active-connection count for ip.
func (t *IPTracker) Release(ip string) {
	t.mu.Lock()
	defer t.mu.Unlock()
	if t.activeCounts[ip] > 0 {
		t.activeCounts[ip]--
	}
}

// HTTPRateLimiter provides per-IP rate limiting for HTTP endpoints.
// Ports 1702 and 1703 sit behind an internal reverse proxy; the real client
// IP must be read from the X-Forwarded-For / X-Real-IP header rather than
// r.RemoteAddr, which will always be 127.0.0.1 for proxied requests.
type HTTPRateLimiter struct {
	mu      sync.Mutex
	buckets map[string]*TokenBucket
}

// NewHTTPRateLimiter creates an HTTPRateLimiter and starts a background
// goroutine that flushes stale per-IP buckets every five minutes.
func NewHTTPRateLimiter() *HTTPRateLimiter {
	rl := &HTTPRateLimiter{buckets: make(map[string]*TokenBucket)}
	go func() {
		for range time.Tick(5 * time.Minute) {
			rl.mu.Lock()
			rl.buckets = make(map[string]*TokenBucket)
			rl.mu.Unlock()
		}
	}()
	return rl
}

// realIP extracts the client IP, preferring X-Forwarded-For / X-Real-IP so
// that the limiter works correctly when requests arrive via the reverse proxy.
func realIP(r *http.Request) string {
	if xff := r.Header.Get("X-Forwarded-For"); xff != "" {
		// X-Forwarded-For may be a comma-separated list; take the first entry.
		if idx := strings.Index(xff, ","); idx != -1 {
			return strings.TrimSpace(xff[:idx])
		}
		return strings.TrimSpace(xff)
	}
	if xri := r.Header.Get("X-Real-IP"); xri != "" {
		return strings.TrimSpace(xri)
	}
	ip, _, _ := net.SplitHostPort(r.RemoteAddr)
	return ip
}

// Middleware wraps an http.Handler with per-IP rate limiting.
func (rl *HTTPRateLimiter) Middleware(next http.Handler) http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		ip := realIP(r)

		rl.mu.Lock()
		bucket, ok := rl.buckets[ip]
		if !ok {
			bucket = NewTokenBucket(10, 2) // burst 10, refill 2/sec
			rl.buckets[ip] = bucket
		}
		rl.mu.Unlock()

		if !bucket.Take() {
			http.Error(w, "Rate limit exceeded", http.StatusTooManyRequests)
			return
		}
		next.ServeHTTP(w, r)
	})
}

// ---------------------------------------------------------------------------

// GalaxyTracker tracks the last activity time for galaxies
type GalaxyTracker struct {
	GalaxyStart     time.Time
	LastActive      time.Time
	TotalShipDamage int
	AdminMode       bool
	MaxSizeX        int
	MaxSizeY        int
	MaxRomulans     int
	DecwarMode      bool
}

// CommandHandler defines a function type for handling commands
type CommandHandler func([]string, net.Conn) string

// Command represents a command with its handler and help text
type Command struct {
	Handler         CommandHandler
	Help            string
	TotalShipDamage int
}

// GameTask represents a player action to be processed atomically
type GameTask struct {
	PlayerID        string
	Command         string
	Args            []string
	RequiresDelay   bool
	DelayDuration   time.Duration
	Response        chan string
	Conn            net.Conn
	Galaxy          uint16
	Writer          *bufio.Writer
	Context         context.Context
	IsStateChanging bool
}

// Galaxy represents a game galaxy with its own command processing
type Galaxy struct {
	ID           uint16
	CommandQueue chan *GameTask
	LastActive   time.Time
	Mutex        sync.Mutex    // Protects galaxy state during command processing
	Objects      []*Object     // All objects owned exclusively by this galaxy's GalaxyEngine
	objectsMu    sync.RWMutex  // Protects Objects; replaces spatialIndexMutex for intra-galaxy use
	Done         chan struct{} // Signal to stop this galaxy's command processor
	rng          *rand.Rand    // Per-galaxy RNG; seeded from crypto/rand at creation time
	// RobotQueue receives robot-task messages after each state-changing human
	// command.  The robot worker goroutine drains it serially so robot actions
	// are never concurrent with each other, but the galaxy's CommandQueue is
	// free to accept new human commands while the robot pass runs.
	RobotQueue chan robotTask
	// SyncDone is closed (then immediately re-created) by processGalaxyCommands
	// after each task batch completes.  Callers waiting for a happens-before
	// guarantee select on the channel returned by BatchDone() instead of sleeping.
	syncDone   chan struct{}
	syncDoneMu sync.Mutex // protects syncDone replacement
}

// robotTask is the message sent to Galaxy.RobotQueue after each state-changing
// human command.  It carries just enough context for robotsUnlocked to run.
type robotTask struct {
	galaxy     uint16
	callerSide string
}

// Interpreter struct
type Interpreter struct {
	pregameCommands map[string]Command
	gowarsCommands  map[string]Command
	programStart    time.Time
	connections     *sync.Map // Map of net.Conn to ConnectionInfo
	writers         *sync.Map // Map of net.Conn to *bufio.Writer
	writerMutexs    *sync.Map // Map of net.Conn to *sync.Mutex

	spatialIndexMutex sync.RWMutex // Mutex for spatial indexing
	objects           []*Object    // Slice of all objects

	// Spatial indexing for O(1) lookups
	objectsByLocation    map[uint16]map[string]*Object   // galaxy -> "x,y" -> Object
	objectsByType        map[uint16]map[string][]*Object // galaxy -> type -> []*Object
	shipsByGalaxyAndName map[uint16]map[string]*Object   // galaxy -> shipname -> Object
	// Must always be locked after galaxiesMutex if both are needed (see lock hierarchy note at top)
	// spatialIndexMutex removed: per-galaxy locking is now via Galaxy.objectsMu

	galaxies      map[uint16]*Galaxy
	galaxiesMutex sync.RWMutex

	// Per-galaxy sync.Once for thread-safe initialization
	galaxyInitOnce      map[uint16]*sync.Once
	galaxyInitOnceMutex sync.Mutex

	galaxyTracker   map[uint16]GalaxyTracker
	trackerMutex    sync.Mutex
	lastSide        string     // Tracks the last side assigned
	lastSideMutex   sync.Mutex // Protects lastSide
	reservedWords   map[string]struct{}
	TotalShipDamage int // Total ship damage for this interpreter

	// Per-galaxy initialization parameters (size, counts, etc.)
	galaxyParams      map[uint16]GalaxyParams
	galaxyParamsMutex sync.RWMutex

	// Destruction cooldown tracking: IP:Port -> Galaxy -> DestructionTime
	destroyedCooldowns      map[string]map[uint16]time.Time
	destroyedCooldownsMutex sync.Mutex

	instanceID int // Unique identifier for this Interpreter instance

	// Legacy global task queue – acts as a safety-net forwarder to per-galaxy queues.
	// All new routing should send directly to galaxy.CommandQueue via getOrCreateGalaxy.
	TaskQueue          chan *GameTask
	stateEngineRunning bool
	shutdown           chan struct{} // Signal to shutdown all state engines (global + per-galaxy)
}

// LockGalaxiesAndSpatialIndex locks galaxiesMutex and then spatialIndexMutex in the correct order.
// Kept for call-site compatibility; spatialIndexMutex removed, so this now only locks galaxiesMutex.
func (i *Interpreter) LockGalaxiesAndSpatialIndex()    { i.galaxiesMutex.Lock() }
func (i *Interpreter) UnlockGalaxiesAndSpatialIndex()  { i.galaxiesMutex.Unlock() }
func (i *Interpreter) RLockGalaxiesAndSpatialIndex()   { i.galaxiesMutex.RLock() }
func (i *Interpreter) RUnlockGalaxiesAndSpatialIndex() { i.galaxiesMutex.RUnlock() }

// galaxyObjects returns the Galaxy and its current Objects slice for the given ID.
// Callers that mutate Objects must additionally hold Galaxy.objectsMu (write).
// Callers that only iterate must hold Galaxy.objectsMu (read).
// Returns (nil, nil) when the galaxy does not exist.
func (i *Interpreter) galaxyObjects(galaxyID uint16) (*Galaxy, []*Object) {
	i.galaxiesMutex.RLock()
	gal := i.galaxies[galaxyID]
	i.galaxiesMutex.RUnlock()
	if gal == nil {
		return nil, nil
	}
	return gal, gal.Objects
}

// =============================================================================
// DAMAGE CALCULATION SYSTEM
// =============================================================================
// This section implements a clean separation of concerns for combat damage:
//
// 1. DamageCalculator: Pure damage calculations without side effects
// 2. DamageResult: Immutable result data from damage calculations
// 3. ApplyDamageResult: Applies calculated damage to game objects
// 4. MessageFormatter: Formats combat messages based on output preferences
// 5. Message Delivery: Sends formatted messages to appropriate connections
//
// This separation allows for:
// - Easy testing of damage calculations in isolation
// - Reusable message formatting for different contexts
// - Clear data flow: Calculate -> Apply -> Format -> Deliver
// =============================================================================

// DamageResult holds the results of a damage calculation
type DamageResult struct {
	Damage            int    // Final damage amount
	ShieldDamage      int    // Damage to shields
	CriticalHit       bool   // Whether this was a critical hit
	CriticalDevice    int    // Which device was critically damaged (1-9)
	CriticalDamageAmt int    // Amount of critical damage
	Deflected         bool   // Whether the attack was deflected
	TargetDestroyed   bool   // Whether the target was destroyed
	ShieldsDown       bool   // Whether shields went down due to this hit
	Message           string // Any special message from the calculation
}

// WeaponType represents the type of weapon used
type WeaponType int

const (
	WeaponTorpedo WeaponType = iota
	WeaponPhaser
	WeaponNova
)

// DamageCalculator handles pure damage calculations without side effects.
// All methods return DamageResult structs and do not modify game state.
type DamageCalculator struct {
	rng *rand.Rand // RNG instance; must be set at construction time
}

// MessageFormatter handles formatting combat messages based on player preferences.
// It takes CombatMessageData and returns formatted strings ready for delivery.
type MessageFormatter struct{}

// FormatCombatMessage formats a combat message based on the provided data
func criticalDeviceName(device int) string {
	switch device {
	case 1:
		return "Deflector Shields"
	case 2:
		return "Warp Engines"
	case 3:
		return "Impulse Engines"
	case 4:
		return "Torpedo Tubes"
	case 5:
		return "Phasers"
	case 6:
		return "Computer"
	case 7:
		return "Life Support"
	case 8:
		return "Radio"
	case 9:
		return "Tractor Beam"
	default:
		return "Unknown Device"
	}
}

func (mf *MessageFormatter) FormatCombatMessage(data CombatMessageData) string {
	var message string
	var tname string

	// Set the name abbreviation for all the cases that abbreviate
	if data.Target.Type == "Planet" {
		if data.Target.Side == "Federation" {
			tname = "+@"
		} else if data.Target.Side == "Empire" {
			tname = "-@"
		} else {
			tname = "@"
		}
	} else if data.Target.Type == "Base" {
		if data.Target.Side == "Federation" {
			tname = "[]"
		} else {
			tname = "()"
		}
	} else if data.Target.Type == "Star" {
		tname = "*"
	} else if data.Target.Type == "Black Hole" {
		tname = " "
	}

	var attackerName string
	if data.Attacker.Type == "Ship" && strings.ToLower(data.Attacker.Side) == "romulan" {
		attackerName = "Romulan"
	} else if data.Attacker.Type == "Ship" {
		attackerName = data.Attacker.Name
	} else {
		attackerName = data.Attacker.Type
	}
	if attackerName == "" {
		attackerName = "Unknown"
	}
	var targetName string
	if data.Target.Type == "Ship" && strings.ToLower(data.Target.Side) == "romulan" {
		targetName = "Romulan"
	} else if data.Target.Type == "Ship" {
		targetName = data.Target.Name
	} else {
		targetName = data.Target.Type
	}
	if targetName == "" {
		targetName = "Unknown"
	}

	var hitAmount int
	if data.WeaponType == WeaponTorpedo {
		hitAmount = data.DamageResult.Damage
	} else if data.WeaponType == WeaponPhaser {
		hitAmount = data.BlastAmount
	} else if data.WeaponType == WeaponNova {
		hitAmount = data.DamageResult.Damage / 10
	}

	switch data.OutputState {
	case "long":
		switch data.OCdef {
		case "both":
			message = mf.formatLongBothMessage(attackerName, targetName, tname, data, hitAmount)
		case "relative":
			message = mf.formatLongRelativeMessage(attackerName, targetName, tname, data, hitAmount)
		case "absolute":
			message = mf.formatLongAbsoluteMessage(attackerName, targetName, tname, data, hitAmount)
		}
	case "medium":
		switch data.OCdef {
		case "both":
			message = mf.formatMediumBothMessage(attackerName, targetName, tname, data, hitAmount)
		case "relative":
			message = mf.formatMediumRelativeMessage(attackerName, targetName, tname, data, hitAmount)
		case "absolute":
			message = mf.formatMediumAbsoluteMessage(attackerName, targetName, tname, data, hitAmount)
		}
	case "short":
		switch data.OCdef {
		case "both":
			message = mf.formatShortBothMessage(attackerName, targetName, tname, data, hitAmount)
		case "relative":
			message = mf.formatShortRelativeMessage(attackerName, targetName, tname, data, hitAmount)
		case "absolute":
			message = mf.formatShortAbsoluteMessage(attackerName, targetName, tname, data, hitAmount)
		}
	}

	// Append device damage information to the message only for the target
	if data.IsTarget && data.DamageResult.CriticalDevice > 0 && data.DamageResult.CriticalDamageAmt > 0 {
		deviceName := criticalDeviceName(data.DamageResult.CriticalDevice)
		critDmgDisplay := float64(data.DamageResult.CriticalDamageAmt) / 100.0
		// Insert the device damage info before the trailing \r\n
		if len(message) >= 2 && message[len(message)-2:] == "\r\n" {
			message = message[:len(message)-2] + fmt.Sprintf("; %s damaged %.1f units\r\n", deviceName, critDmgDisplay)
		} else {
			message += fmt.Sprintf("; %s damaged %.1f units\r\n", deviceName, critDmgDisplay)
		}
	}

	return message
}

// Long format messages
func (mf *MessageFormatter) formatLongBothMessage(attackerName, targetName, tname string, data CombatMessageData, hitAmount int) string {
	var message string

	if data.WeaponType == WeaponPhaser {

		if (data.OutputState == "long" || data.OutputState == "medium") && data.Attacker.Type != "Planet" && data.Attacker.Type != "Base" && data.Attacker.Side != "romulan" {
			message = "High speed shield control activated.\r\n"
		}
		attackerPart := fmt.Sprintf("%s @%d-%d %+d,%+d %s%.1f%%", attackerName, data.Attacker.LocationX, data.Attacker.LocationY, data.AttackerRelativeX, data.AttackerRelativeY, boolToSign(data.Attacker.ShieldsUpDown), data.AttackerShields)
		totalDamage := float64(data.DamageResult.ShieldDamage)/10.0 + float64(data.DamageResult.Damage)/100.0
		energyPart := fmt.Sprintf("%.1f phaser hit on", totalDamage)
		targetPart := fmt.Sprintf("%s @%d-%d %+d,%+d %s%.1f%%", targetName, data.Target.LocationX, data.Target.LocationY, data.RelativeX, data.RelativeY, boolToSign(data.Target.ShieldsUpDown), data.TargetShields)
		message += fmt.Sprintf("%s makes %s %s\r\n", attackerPart, energyPart, targetPart)
	} else {
		if data.WeaponType == WeaponTorpedo {
			message = fmt.Sprintf("%s @%d-%d %+d,%+d %s%.1f%% ", attackerName, data.Attacker.LocationX, data.Attacker.LocationY, data.AttackerRelativeX, data.AttackerRelativeY, boolToSign(data.Attacker.ShieldsUpDown), data.AttackerShields)
			if data.DamageResult.Deflected {
				message += "has torpedo deflected by "
			} else {
				message += fmt.Sprintf("makes %d unit torpedo hit on ", hitAmount/10)
			}
			message += fmt.Sprintf("%s @%d-%d %+d,%+d %s%.1f%%\r\n", targetName, data.Target.LocationX, data.Target.LocationY, data.RelativeX, data.RelativeY, boolToSign(data.Target.ShieldsUpDown), data.TargetShields)
		} else { // nova
			message = fmt.Sprintf("%s @%d-%d %s%.1f%% ", attackerName, data.Attacker.LocationX, data.Attacker.LocationY, boolToSign(data.Attacker.ShieldsUpDown), data.AttackerShields)
			if data.DamageResult.Deflected {
				message += "has nova deflected by "
			} else {
				message += fmt.Sprintf("makes %d unit hit on ", hitAmount/10)
			}
			if data.Displaced {
				message += fmt.Sprintf("%s displaced @%d-%d %+d,%+d %s%.1f%%\r\n", targetName, data.Target.LocationX, data.Target.LocationY, data.RelativeX, data.RelativeY, boolToSign(data.Target.ShieldsUpDown), data.TargetShields)
			} else {
				message += fmt.Sprintf("%s @%d-%d %+d,%+d %s%.1f%%\r\n", targetName, data.Target.LocationX, data.Target.LocationY, data.RelativeX, data.RelativeY, boolToSign(data.Target.ShieldsUpDown), data.TargetShields)
			}
		}
	}
	return message
}

func (mf *MessageFormatter) formatLongRelativeMessage(attackerName, targetName, tname string, data CombatMessageData, hitAmount int) string {
	var message string
	if data.WeaponType == WeaponPhaser {
		if (data.OutputState == "long" || data.OutputState == "medium") && data.Attacker.Type != "Planet" && data.Attacker.Type != "Base" && data.Attacker.Side != "romulan" {
			message = "High speed shield control activated.\r\n"
		}
		attackerPart := fmt.Sprintf("%s %+d,%+d %s%.1f%%", attackerName, data.AttackerRelativeX, data.AttackerRelativeY, boolToSign(data.Attacker.ShieldsUpDown), data.AttackerShields)
		totalDamage := float64(data.DamageResult.ShieldDamage)/10.0 + float64(data.DamageResult.Damage)/100.0
		energyPart := fmt.Sprintf("%.1f phaser hit on", totalDamage)
		targetPart := fmt.Sprintf("%s %+d,%+d %s%.1f%%", targetName, data.RelativeX, data.RelativeY, boolToSign(data.Target.ShieldsUpDown), data.TargetShields)
		message += fmt.Sprintf("%s makes %s %s\r\n", attackerPart, energyPart, targetPart)
	} else {
		if data.WeaponType == WeaponTorpedo {
			message = fmt.Sprintf("%s %+d,%+d %s%.1f%% ", attackerName, data.AttackerRelativeX, data.AttackerRelativeY, boolToSign(data.Attacker.ShieldsUpDown), data.AttackerShields)
			if data.DamageResult.Deflected {
				message += "has torpedo deflected by "
			} else {
				message += fmt.Sprintf("makes %d unit torpedo hit on ", hitAmount/10)
			}
			message += fmt.Sprintf("%s %+d,%+d %s%.1f%%\r\n", targetName, data.RelativeX, data.RelativeY, boolToSign(data.Target.ShieldsUpDown), data.TargetShields)
		} else {
			message = fmt.Sprintf("%s @%d-%d %s%.1f%% ", attackerName, data.Attacker.LocationX, data.Attacker.LocationY, boolToSign(data.Attacker.ShieldsUpDown), data.AttackerShields)
			if data.DamageResult.Deflected {
				message += "has nova deflected by "
			} else {
				message += fmt.Sprintf("makes %d unit hit on ", hitAmount)
			}
			message += fmt.Sprintf("%s %+d,%+d %s%.1f%%\r\n", targetName, data.RelativeX, data.RelativeY, boolToSign(data.Target.ShieldsUpDown), data.TargetShields)

		}
	}
	return message
}

func (mf *MessageFormatter) formatLongAbsoluteMessage(attackerName, targetName, tname string, data CombatMessageData, hitAmount int) string {
	var message string
	if data.WeaponType == WeaponPhaser {
		if (data.OutputState == "long" || data.OutputState == "medium") && data.Attacker.Type != "Planet" && data.Attacker.Type != "Base" && data.Attacker.Side != "romulan" {
			message = "High speed shield control activated.\r\n"
		}
		attackerPart := fmt.Sprintf("%s @%d-%d %s%.1f%%", attackerName, data.Attacker.LocationX, data.Attacker.LocationY, boolToSign(data.Attacker.ShieldsUpDown), data.AttackerShields)
		totalDamage := float64(data.DamageResult.ShieldDamage)/10.0 + float64(data.DamageResult.Damage)/100.0
		energyPart := fmt.Sprintf("%.1f phaser hit on", totalDamage)
		targetPart := fmt.Sprintf("%s @%d-%d %s%.1f%%", targetName, data.Target.LocationX, data.Target.LocationY, boolToSign(data.Target.ShieldsUpDown), data.TargetShields)
		message += fmt.Sprintf("%s makes %s %s\r\n", attackerPart, energyPart, targetPart)
	} else {
		if data.WeaponType == WeaponTorpedo {
			message = fmt.Sprintf("%s @%d-%d %s%.1f%% ", attackerName, data.Attacker.LocationX, data.Attacker.LocationY, boolToSign(data.Attacker.ShieldsUpDown), data.AttackerShields)
			if data.DamageResult.Deflected {
				message += "has torpedo deflected by "
			} else {
				message += fmt.Sprintf("makes %d unit torpedo hit on ", hitAmount/10)
			}
			message += fmt.Sprintf("%s @%d-%d %s%.1f%%\r\n", targetName, data.Target.LocationX, data.Target.LocationY, boolToSign(data.Target.ShieldsUpDown), data.TargetShields)
		} else {
			message = fmt.Sprintf("%s @%d-%d %s%.1f%% ", attackerName, data.Attacker.LocationX, data.Attacker.LocationY, boolToSign(data.Attacker.ShieldsUpDown), data.AttackerShields)
			if data.DamageResult.Deflected {
				message += "has nova deflected by "
			} else {
				message += fmt.Sprintf("makes %d unit hit on ", hitAmount/10)
			}
			message += fmt.Sprintf("%s @%d-%d %s%.1f%%\r\n", targetName, data.Target.LocationX, data.Target.LocationY, boolToSign(data.Target.ShieldsUpDown), data.TargetShields)

		}
	}
	return message
}

// Medium format messages
func (mf *MessageFormatter) formatMediumBothMessage(attackerName, targetName, tname string, data CombatMessageData, hitAmount int) string {
	var message string
	if data.WeaponType == WeaponPhaser {
		if (data.OutputState == "long" || data.OutputState == "medium") && data.Attacker.Type != "Planet" && data.Attacker.Type != "Base" && data.Attacker.Side != "romulan" {
			message = "High speed shield control activated.\r\n"
		}
		totalDamage := int(float64(data.DamageResult.ShieldDamage)/10.0 + float64(data.DamageResult.Damage)/100.0)
		attackerPart := fmt.Sprintf("%c @%d-%d %+d,%+d %s%.1f%% %dP", attackerName[0], data.Attacker.LocationX, data.Attacker.LocationY, data.AttackerRelativeX, data.AttackerRelativeY, boolToSign(data.Attacker.ShieldsUpDown), data.AttackerShields, totalDamage)
		targetPart := fmt.Sprintf("%c @%d-%d %+d,%+d %s%.1f%%", targetName[0], data.Target.LocationX, data.Target.LocationY, data.RelativeX, data.RelativeY, boolToSign(data.Target.ShieldsUpDown), data.TargetShields)
		message += fmt.Sprintf("%s %s\r\n", attackerPart, targetPart)
	} else {
		if data.WeaponType == WeaponTorpedo {
			message = fmt.Sprintf("%c @%d-%d %+d,%+d %s%.1f%% ", attackerName[0], data.Attacker.LocationX, data.Attacker.LocationY, data.AttackerRelativeX, data.AttackerRelativeY, boolToSign(data.Attacker.ShieldsUpDown), data.AttackerShields)
			if data.DamageResult.Deflected {
				message += "deflected T "
			} else {
				message += fmt.Sprintf("%d unit T ", hitAmount/10)
			}
			message += fmt.Sprintf("%c @%d-%d %+d,%+d %s%.1f%%\r\n", targetName[0], data.Target.LocationX, data.Target.LocationY, data.RelativeX, data.RelativeY, boolToSign(data.Target.ShieldsUpDown), data.TargetShields)
		} else {
			message = fmt.Sprintf("%c @%d-%d %s%.1f%% ", attackerName[0], data.Attacker.LocationX, data.Attacker.LocationY, boolToSign(data.Attacker.ShieldsUpDown), data.AttackerShields)
			if data.DamageResult.Deflected {
				message += "deflected N "
			} else {
				message += fmt.Sprintf("%d unit N ", data.DamageResult.Damage)
			}
			message += fmt.Sprintf("%c @%d-%d %+d,%+d %s%.1f%%\r\n", targetName[0], data.Target.LocationX, data.Target.LocationY, data.RelativeX, data.RelativeY, boolToSign(data.Target.ShieldsUpDown), data.TargetShields)
		}
	}
	return message
}

func (mf *MessageFormatter) formatMediumRelativeMessage(attackerName, targetName, tname string, data CombatMessageData, hitAmount int) string {
	var message string
	if data.WeaponType == WeaponPhaser {
		if (data.OutputState == "long" || data.OutputState == "medium") && data.Attacker.Type != "Planet" && data.Attacker.Type != "Base" && data.Attacker.Side != "romulan" {
			message = "High speed shield control activated.\r\n"
		}
		totalDamage := int(float64(data.DamageResult.ShieldDamage)/10.0 + float64(data.DamageResult.Damage)/100.0)
		attackerPart := fmt.Sprintf("%c %+d,%+d %s%.1f%% %dP", attackerName[0], data.AttackerRelativeX, data.AttackerRelativeY, boolToSign(data.Attacker.ShieldsUpDown), data.AttackerShields, totalDamage)
		targetPart := fmt.Sprintf("%c %+d,%+d %s%.1f%%", targetName[0], data.RelativeX, data.RelativeY, boolToSign(data.Target.ShieldsUpDown), data.TargetShields)
		message += fmt.Sprintf("%s %s\r\n", attackerPart, targetPart)
	} else {
		if data.WeaponType == WeaponTorpedo {
			message = fmt.Sprintf("%c %+d,%+d %s%.1f%% ", attackerName[0], data.AttackerRelativeX, data.AttackerRelativeY, boolToSign(data.Attacker.ShieldsUpDown), data.AttackerShields)
			if data.DamageResult.Deflected {
				message += "deflected T "
			} else {
				message += fmt.Sprintf("%d unit T ", hitAmount/10)
			}
			message += fmt.Sprintf("%c %+d,%+d %s%.1f%%\r\n", targetName[0], data.RelativeX, data.RelativeY, boolToSign(data.Target.ShieldsUpDown), data.TargetShields)
		} else {
			message = fmt.Sprintf("%c %s%.1f%% ", attackerName[0], boolToSign(data.Attacker.ShieldsUpDown), data.AttackerShields)
			if data.DamageResult.Deflected {
				message += "deflected N "
			} else {
				message += fmt.Sprintf("%d unit N ", data.DamageResult.Damage)
			}
			message += fmt.Sprintf("%c %+d,%+d %s%.1f%%\r\n", targetName[0], data.RelativeX, data.RelativeY, boolToSign(data.Target.ShieldsUpDown), data.TargetShields)
		}
	}
	return message
}

func (mf *MessageFormatter) formatMediumAbsoluteMessage(attackerName, targetName, tname string, data CombatMessageData, hitAmount int) string {
	var message string
	if data.WeaponType == WeaponPhaser {
		if (data.OutputState == "long" || data.OutputState == "medium") && data.Attacker.Type != "Planet" && data.Attacker.Type != "Base" && data.Attacker.Side != "romulan" {
			message = "High speed shield control activated.\r\n"
		}
		totalDamage := int(float64(data.DamageResult.ShieldDamage)/10.0 + float64(data.DamageResult.Damage)/100.0)
		attackerPart := fmt.Sprintf("%c @%d-%d %s%.1f%% %dP", attackerName[0], data.Attacker.LocationX, data.Attacker.LocationY, boolToSign(data.Attacker.ShieldsUpDown), data.AttackerShields, totalDamage)
		targetPart := fmt.Sprintf("%c @%d-%d %s%.1f%%", targetName[0], data.Target.LocationX, data.Target.LocationY, boolToSign(data.Target.ShieldsUpDown), data.TargetShields)
		message += fmt.Sprintf("%s %s\r\n", attackerPart, targetPart)
	} else {
		if data.WeaponType == WeaponTorpedo {
			message = fmt.Sprintf("%c @%d-%d %s%.1f%% ", attackerName[0], data.Attacker.LocationX, data.Attacker.LocationY, boolToSign(data.Attacker.ShieldsUpDown), data.AttackerShields)
			if data.DamageResult.Deflected {
				message += "deflected T "
			} else {
				message += fmt.Sprintf("%d unit T ", hitAmount/10)
			}
			message += fmt.Sprintf("%c @%d-%d %s%.1f%%\r\n", targetName[0], data.Target.LocationX, data.Target.LocationY, boolToSign(data.Target.ShieldsUpDown), data.TargetShields)
		} else {
			message = fmt.Sprintf("%c @%d-%d %s%.1f%% ", attackerName[0], data.Attacker.LocationX, data.Attacker.LocationY, boolToSign(data.Attacker.ShieldsUpDown), data.AttackerShields)
			if data.DamageResult.Deflected {
				message += "deflected N "
			} else {
				message += fmt.Sprintf("%d unit N ", data.DamageResult.Damage)
			}
			message += fmt.Sprintf("%c @%d-%d %s%.1f%%\r\n", targetName[0], data.Target.LocationX, data.Target.LocationY, boolToSign(data.Target.ShieldsUpDown), data.TargetShields)
		}
	}
	return message
}

// Short format messages
func (mf *MessageFormatter) formatShortBothMessage(attackerName, targetName, tname string, data CombatMessageData, hitAmount int) string {
	var message string
	if data.WeaponType == WeaponPhaser {
		totalDamage := int(float64(data.DamageResult.ShieldDamage)/10.0 + float64(data.DamageResult.Damage)/100.0)
		attackerPart := fmt.Sprintf("%c @%d-%d, %+d,%+d %s%.1f%% %dP", attackerName[0], data.Attacker.LocationX, data.Attacker.LocationY, data.AttackerRelativeX, data.AttackerRelativeY, boolToSign(data.Attacker.ShieldsUpDown), data.AttackerShields, totalDamage)
		targetPart := fmt.Sprintf("%c @%d-%d %+d,%+d %s%.1f%%", targetName[0], data.Target.LocationX, data.Target.LocationY, data.RelativeX, data.RelativeY, boolToSign(data.Target.ShieldsUpDown), data.TargetShields)
		message += fmt.Sprintf("%s %s\r\n", attackerPart, targetPart)
	} else {
		if data.WeaponType == WeaponTorpedo {
			message = fmt.Sprintf("%c @%d-%d %+d,%+d %s%.1f%% ", attackerName[0], data.Attacker.LocationX, data.Attacker.LocationY, data.AttackerRelativeX, data.AttackerRelativeY, boolToSign(data.Attacker.ShieldsUpDown), data.AttackerShields)
			if data.DamageResult.Deflected {
				message += "T deflected by "
			} else {
				message += fmt.Sprintf("%d T ", hitAmount)
			}
			message += fmt.Sprintf("%c @%d-%d %+d,%+d\r\n", targetName[0], data.Target.LocationX, data.Target.LocationY, data.RelativeX, data.RelativeY)
		} else {
			message = fmt.Sprintf("%c @%d-%d %s%.1f%% ", attackerName[0], data.Attacker.LocationX, data.Attacker.LocationY, boolToSign(data.Attacker.ShieldsUpDown), data.AttackerShields)
			if data.DamageResult.Deflected {
				message += "N deflected by "
			} else {
				message += fmt.Sprintf("%d N ", data.DamageResult.Damage)
			}
			message += fmt.Sprintf("%c @%d-%d %+d,%+d\r\n", targetName[0], data.Target.LocationX, data.Target.LocationY, data.RelativeX, data.RelativeY)

		}
	}
	return message
}

func (mf *MessageFormatter) formatShortRelativeMessage(attackerName, targetName, tname string, data CombatMessageData, hitAmount int) string {
	var message string
	if data.WeaponType == WeaponPhaser {
		totalDamage := int(float64(data.DamageResult.ShieldDamage)/10.0 + float64(data.DamageResult.Damage)/100.0)
		attackerPart := fmt.Sprintf("%c %+d,%+d %s%.1f%% %dP", attackerName[0], data.AttackerRelativeX, data.AttackerRelativeY, boolToSign(data.Attacker.ShieldsUpDown), data.AttackerShields, totalDamage)
		targetPart := fmt.Sprintf("%c %+d,%+d %s%.1f%%", targetName[0], data.RelativeX, data.RelativeY, boolToSign(data.Target.ShieldsUpDown), data.TargetShields)
		message += fmt.Sprintf("%s %s\r\n", attackerPart, targetPart)
	} else {
		if data.WeaponType == WeaponTorpedo {
			message = fmt.Sprintf("%c %+d,%+d %s%.1f%% ", attackerName[0], data.AttackerRelativeX, data.AttackerRelativeY, boolToSign(data.Attacker.ShieldsUpDown), data.AttackerShields)
			if data.DamageResult.Deflected {
				message += "T deflected by "
			} else {
				message += fmt.Sprintf("%d T ", hitAmount)
			}
			message += fmt.Sprintf("%c %+d,%+d %s%.1f%%\r\n", targetName[0], data.RelativeX, data.RelativeY, boolToSign(data.Target.ShieldsUpDown), data.TargetShields)
		} else {
			message = fmt.Sprintf("%c %s%.1f%% ", attackerName[0], boolToSign(data.Attacker.ShieldsUpDown), data.AttackerShields)
			if data.DamageResult.Deflected {
				message += "N deflected by "
			} else {
				message += fmt.Sprintf("%d N ", data.DamageResult.Damage)
			}
			message += fmt.Sprintf("%c %+d,%+d %s%.1f%%\r\n", targetName[0], data.RelativeX, data.RelativeY, boolToSign(data.Target.ShieldsUpDown), data.TargetShields)

		}
	}
	return message
}

func (mf *MessageFormatter) formatShortAbsoluteMessage(attackerName, targetName, tname string, data CombatMessageData, hitAmount int) string {
	var message string
	if data.WeaponType == WeaponPhaser {
		totalDamage := int(float64(data.DamageResult.ShieldDamage)/10.0 + float64(data.DamageResult.Damage)/100.0)
		attackerPart := fmt.Sprintf("%c @%d-%d %s%.1f%% %dP", attackerName[0], data.Attacker.LocationX, data.Attacker.LocationY, boolToSign(data.Attacker.ShieldsUpDown), data.AttackerShields, totalDamage)
		targetPart := fmt.Sprintf("%c @%d-%d %s%.1f%%", targetName[0], data.Target.LocationX, data.Target.LocationY, boolToSign(data.Target.ShieldsUpDown), data.TargetShields)
		message += fmt.Sprintf("%s %s\r\n", attackerPart, targetPart)
	} else {
		if data.WeaponType == WeaponTorpedo {
			message = fmt.Sprintf("%c @%d-%d %s%.1f%% ", attackerName[0], data.Attacker.LocationX, data.Attacker.LocationY, boolToSign(data.Attacker.ShieldsUpDown), data.AttackerShields)
			if data.DamageResult.Deflected {
				message += "T deflected by "
			} else {
				message += fmt.Sprintf("%d T ", hitAmount)
			}
			message += fmt.Sprintf("%c @%d-%d %s%.1f%%\r\n", targetName[0], data.Target.LocationX, data.Target.LocationY, boolToSign(data.Target.ShieldsUpDown), data.TargetShields)
		} else {
			message = fmt.Sprintf("%c @%d-%d %s%.1f%% ", attackerName[0], data.Attacker.LocationX, data.Attacker.LocationY, boolToSign(data.Attacker.ShieldsUpDown), data.AttackerShields)
			if data.DamageResult.Deflected {
				message += "T deflected by "
			} else {
				message += fmt.Sprintf("%d T ", data.DamageResult.Damage)
			}
			message += fmt.Sprintf("%c @%d-%d %s%.1f%%\r\n", targetName[0], data.Target.LocationX, data.Target.LocationY, boolToSign(data.Target.ShieldsUpDown), data.TargetShields)
		}
	}
	return message
}

// CombatMessageData holds all data needed for message formatting
type CombatMessageData struct {
	Attacker          *Object
	Target            *Object
	DamageResult      DamageResult
	WeaponType        WeaponType
	BlastAmount       int
	RelativeX         int
	RelativeY         int
	AttackerRelativeX int
	AttackerRelativeY int
	OutputState       string
	OCdef             string
	AttackerShields   float64
	TargetShields     float64
	Displaced         bool // Indicates if the ship was displaced by a nova
	IsTarget          bool // True when the observer receiving this message is the target
}

// CombatEvent represents a combat event that occurred
type CombatEvent struct {
	Galaxy            uint16
	AttackerIdx       int
	TargetIdx         int
	Weapon            string // "Phaser" or "Torpedo"
	Damage            int
	Message           string
	CriticalHit       bool
	CriticalDevice    int
	CriticalDamageAmt int
}

// BroadcastCombatEvent broadcasts a combat event to all relevant players in the galaxy.
// It sends a formatted combat message to:
// 1. The attacker who initiated the combat (if playerConn belongs to attacker)
// 2. All ships within scan range of the target
// This function replaces the need to call both HitMsg and AnnounceMsg separately.
func (i *Interpreter) BroadcastCombatEvent(event *CombatEvent, playerConn net.Conn) {
	i.BroadcastCombatEventWithInitiator(event, playerConn, playerConn)
}

// BroadcastCombatEventNoLock broadcasts a combat event when objectsMutex is already held
// The caller must hold objectsMutex
func (i *Interpreter) BroadcastCombatEventNoLock(event *CombatEvent) {
	// Defensive: check indices before accessing objects slice
	if event.AttackerIdx < 0 || event.AttackerIdx >= len(i.objects) {
		log.Printf("BroadcastCombatEventNoLock: invalid AttackerIdx %d (objects len=%d)", event.AttackerIdx, len(i.objects))
		return
	}
	if event.TargetIdx < 0 || event.TargetIdx >= len(i.objects) {
		log.Printf("BroadcastCombatEventNoLock: invalid TargetIdx %d (objects len=%d)", event.TargetIdx, len(i.objects))
		return
	}
	attacker := i.objects[event.AttackerIdx]
	target := i.objects[event.TargetIdx]

	// Get galaxy from the attacker
	galaxy := attacker.Galaxy

	// 1. Send combat hit message to attacker and target (if they are ships)
	for _, obj := range []*Object{attacker, target} {
		if obj.Type == "Ship" {
			i.connections.Range(func(key, value interface{}) bool {
				conn := key.(net.Conn)
				ci := value.(ConnectionInfo)
				if ci.Shipname == obj.Name && ci.Galaxy == obj.Galaxy {
					i.sendCombatMessageToConnection(event, conn, attacker, target, ci, false)
					return false // Only send once per ship
				}
				return true
			})
		}
	}

	// 2. Notify nearby witnesses (excluding attacker and target)
	ships := i.getObjectsByType(galaxy, "Ship")
	if ships != nil {
		for _, obj := range ships {
			if obj.Name == attacker.Name || obj.Name == target.Name {
				continue // Skip attacker and target
			}
			if (obj.LocationX >= target.LocationX-(DefScanRange/2) && obj.LocationX <= target.LocationX+(DefScanRange/2)) &&
				(obj.LocationY >= target.LocationY-(DefScanRange/2) && obj.LocationY <= target.LocationY+(DefScanRange/2)) {
				i.connections.Range(func(key, value interface{}) bool {
					conn := key.(net.Conn)
					ci := value.(ConnectionInfo)
					if ci.Shipname == obj.Name && ci.Galaxy == obj.Galaxy {
						i.sendCombatMessageToConnection(event, conn, attacker, target, ci, false)
						return false
					}
					return true
				})
			}
		}
	}
}

// BroadcastCombatEventWithInitiator broadcasts a combat event, tracking who initiated the command
func (i *Interpreter) BroadcastCombatEventWithInitiator(event *CombatEvent, playerConn net.Conn, initiatingConn net.Conn) {
	// Validate indices before accessing i.objects
	if event.AttackerIdx < 0 || event.AttackerIdx >= len(i.objects) || event.TargetIdx < 0 || event.TargetIdx >= len(i.objects) {
		log.Printf("Invalid indices in BroadcastCombatEventWithInitiator: AttackerIdx=%d, TargetIdx=%d, len(i.objects)=%d", event.AttackerIdx, event.TargetIdx, len(i.objects))
		return
	}

	attacker := i.objects[event.AttackerIdx]
	target := i.objects[event.TargetIdx]

	if playerConn == nil {
		galaxy := attacker.Galaxy

		// 1. Send messages to attacker and target if they are ships
		for _, obj := range []*Object{attacker, target} {
			if obj.Type == "Ship" {
				i.connections.Range(func(key, value interface{}) bool {
					conn := key.(net.Conn)
					ci := value.(ConnectionInfo)
					if ci.Shipname == obj.Name && ci.Galaxy == obj.Galaxy {
						i.sendCombatMessageToConnection(event, conn, attacker, target, ci, false)
						return false // Only send once per ship
					}
					return true
				})
			}
		}

		// 2. Notify nearby witnesses
		ships := i.getObjectsByType(galaxy, "Ship")
		if ships != nil {
			for _, obj := range ships {
				if obj.Name == attacker.Name || obj.Name == target.Name {
					continue // Skip attacker and target (they already got direct messages above)
				}
				if (obj.LocationX >= target.LocationX-(DefScanRange/2) && obj.LocationX <= target.LocationX+(DefScanRange/2)) &&
					(obj.LocationY >= target.LocationY-(DefScanRange/2) && obj.LocationY <= target.LocationY+(DefScanRange/2)) {
					i.connections.Range(func(key, value interface{}) bool {
						conn := key.(net.Conn)
						ci := value.(ConnectionInfo)
						if ci.Shipname == obj.Name && ci.Galaxy == obj.Galaxy {
							i.sendCombatMessageToConnection(event, conn, attacker, target, ci, false)
							return false
						}
						return true
					})
				}
			}
		}
		return
	}

	playerConnInfo, ok := i.connections.Load(playerConn)
	if !ok {
		return
	}
	connInfo := playerConnInfo.(ConnectionInfo)
	galaxy := connInfo.Galaxy

	// 1. Send combat hit message to attacker and target
	for _, obj := range []*Object{attacker, target} {
		i.connections.Range(func(key, value interface{}) bool {
			conn := key.(net.Conn)
			ci := value.(ConnectionInfo)
			if obj.Type == "Ship" && obj.Name == ci.Shipname && ci.Galaxy == obj.Galaxy {
				i.sendCombatMessageToConnection(event, conn, attacker, target, ci, conn == initiatingConn)
				return false // Only send once per ship
			}
			return true
		})
	}

	// 2. Notify nearby witnesses (excluding attacker and target)
	ships := i.getObjectsByType(galaxy, "Ship")
	if ships != nil {
		for _, obj := range ships {
			if obj.Name == attacker.Name || obj.Name == target.Name {
				continue // Skip attacker and target
			}
			if (obj.LocationX >= target.LocationX-(DefScanRange/2) && obj.LocationX <= target.LocationX+(DefScanRange/2)) &&
				(obj.LocationY >= target.LocationY-(DefScanRange/2) && obj.LocationY <= target.LocationY+(DefScanRange/2)) {
				i.connections.Range(func(key, value interface{}) bool {
					conn := key.(net.Conn)
					ci := value.(ConnectionInfo)
					if ci.Shipname == obj.Name && ci.Galaxy == obj.Galaxy {
						i.sendCombatMessageToConnection(event, conn, attacker, target, ci, conn == initiatingConn)
						return false
					}
					return true
				})
			}
		}
	}

	// 3. If the target was destroyed, broadcast destruction ONCE
	if event.Message == "destroyed" || (target.Condition == "Destroyed") {
		// Place your destruction notification logic here
		// Example: i.AnnounceMsg(fmt.Sprintf("%s was destroyed!", target.Name))
	}
}

// sendCombatMessageToConnection sends a formatted combat message to a specific connection
func (i *Interpreter) sendCombatMessageToConnection(event *CombatEvent, conn net.Conn, attacker, target *Object, connInfo ConnectionInfo, isInitiatingPlayer bool) {
	i.sendCombatMessageToConnectionWithDisplacement(event, conn, attacker, target, connInfo, isInitiatingPlayer, false)
}

// sendCombatMessageToConnectionWithDisplacement allows specifying if the target was displaced (for nova hits)
func (i *Interpreter) sendCombatMessageToConnectionWithDisplacement(event *CombatEvent, conn net.Conn, attacker, target *Object, connInfo ConnectionInfo, isInitiatingPlayer bool, displaced bool) {
	// Calculate shield percentages
	var attackerShieldPct float64
	if attacker.Shields > 0 {
		attackerShieldPct = (float64(attacker.Shields) / float64(InitialShieldValue)) * 100.0
	}

	var targetShieldPct float64
	targetShieldPct = float64(target.Shields) / float64(InitialShieldValue) * 100.0

	// Calculate relative position from observer to target using direct ship pointer
	// Check if the receiving ship's radio is ON; if not, skip sending the message
	if connInfo.Ship != nil && !connInfo.Ship.RadioOnOff {
		return
	}

	var relativeX, relativeY int
	var attackerRelativeX, attackerRelativeY int
	if connInfo.Ship != nil {
		relativeX = target.LocationX - connInfo.Ship.LocationX
		relativeY = target.LocationY - connInfo.Ship.LocationY
		attackerRelativeX = attacker.LocationX - connInfo.Ship.LocationX
		attackerRelativeY = attacker.LocationY - connInfo.Ship.LocationY
	}

	// Create damage result
	damageResult := DamageResult{
		Damage:            event.Damage,
		Deflected:         event.Damage == 0 && event.Message != "",
		CriticalHit:       event.CriticalHit,
		CriticalDevice:    event.CriticalDevice,
		CriticalDamageAmt: event.CriticalDamageAmt,
	}

	// Determine weapon type
	var weaponType WeaponType
	if event.Weapon == "Phaser" {
		weaponType = WeaponPhaser
	} else {
		if event.Weapon == "Torpedo" {
			weaponType = WeaponTorpedo
		} else {
			weaponType = WeaponNova
		}
	}

	// Create message data
	messageData := CombatMessageData{
		Attacker:          attacker,
		Target:            target,
		DamageResult:      damageResult,
		WeaponType:        weaponType,
		BlastAmount:       event.Damage, // Using damage as blast amount for now
		RelativeX:         relativeX,
		RelativeY:         relativeY,
		AttackerRelativeX: attackerRelativeX,
		AttackerRelativeY: attackerRelativeY,
		OutputState:       connInfo.OutputState,
		OCdef:             connInfo.OCdef,
		AttackerShields:   attackerShieldPct,
		TargetShields:     targetShieldPct,
		Displaced:         displaced,
		IsTarget:          connInfo.Shipname == target.Name,
	}

	// Format message
	formatter := &MessageFormatter{}
	message := formatter.FormatCombatMessage(messageData)

	// Send the message
	if writerRaw, ok := i.writers.Load(conn); ok {
		writer := writerRaw.(*bufio.Writer)
		i.writeBaudf(conn, writer, "%s", message)

		// Re-draw the player's prompt if this isn't the initiating player
		// The initiating player will get their prompt redrawn by the command handler
		if !isInitiatingPlayer {
			prompt := i.getPrompt(conn)
			if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
				mutex := mutexRaw.(*sync.Mutex)
				mutex.Lock()
				writer.WriteString(prompt)
				writer.Flush()
				mutex.Unlock()
			}
		}
	}
}

// NewDamageCalculator creates a new damage calculator using the supplied RNG.
// Pass the galaxy's rng field so all combat randomness is lock-free.
func NewDamageCalculator(rng *rand.Rand) *DamageCalculator {
	return &DamageCalculator{rng: rng}
}

// CalculateTorpedoDamage calculates torpedo damage without applying it.
// Returns a DamageResult with all calculated values including deflection status.
func (dc *DamageCalculator) CalculateTorpedoDamage(target *Object) DamageResult {
	result := DamageResult{}

	// Fortran: hit = 4000.0 + 4000.0 * ran(0)
	hit := 4000.0 + 4000.0*dc.rng.Float64()
	rand1 := dc.rng.Float64()
	rana := dc.rng.Float64()

	// Fortran deflection logic: rand = rana - (shield * 0.001 * rand) + 0.1
	// If rand > 0: torpedo PENETRATES shields (goto 100 for damage calculation)
	// If rand <= 0: torpedo DEFLECTED by shields (reduce shields, no damage)
	shieldStrength := (float64(target.Shields) / float64(InitialShieldValue)) * 1000.0
	deflectionRand := rana - (shieldStrength * 0.001 * rand1) + 0.1
	if target.ShieldsUpDown && target.Shields > 0 && deflectionRand <= 0.0 {
		// Deflected: reduce shields by 50 * rana, no damage
		shieldReduction := int(50.0 * rana)
		if shieldReduction > target.Shields {
			shieldReduction = target.Shields
		}
		result.ShieldDamage = shieldReduction
		result.Deflected = true
		result.Message = "Torpedo deflected by shields"
		return result
	}

	// Not deflected: calculate damage passed through shields
	var hita float64
	if target.ShieldsUpDown && target.Shields > 0 {
		// Fortran: hita = hit * (1000.0 - shield) * 0.001
		// Corrected shield scaling in CalculateTorpedoDamage
		shieldStrength := (float64(target.Shields) / float64(InitialShieldValue)) * 1000.0
		hita = math.Max(0, hit*(1000.0-shieldStrength)*0.001)

		// Fortran: shield = shield - (hit * max(shield * 0.001, 0.1) + 10) * 0.03
		shieldDamageAmount := (hit*math.Max(shieldStrength*0.001, 0.1) + 10.0) * 0.03
		result.ShieldDamage = int(shieldDamageAmount)
	} else {
		// Shields down or destroyed - full damage
		hita = hit
	}

	// Critical hit logic (Fortran: if hita * (rana + 0.1) >= 1700.0)
	if hita*(rana+0.1) >= 1700.0 {
		result.CriticalHit = true
		// Fortran: hita = hita / 2.0 (for critical device hit)
		hita = hita / 2.0
		result.CriticalDevice = dc.rng.Intn(9) + 1 // device 1-9
		hita = hita + (dc.rng.Float64()-0.5)*1000.0
		result.CriticalDamageAmt = int(hita)
	}

	result.Damage = int(hita)
	result.TargetDestroyed = target.TotalShipDamage+result.Damage >= CriticalShipDamage || target.ShipEnergy-result.Damage/10 <= 0

	return result
}

// CalculatePhaserDamage calculates phaser damage without applying it.
// Takes into account range, target type, shields, and critical hit chances.
func (dc *DamageCalculator) CalculatePhaserDamage(target *Object, attacker *Object, blastAmt int, phaserRange int) DamageResult {
	result := DamageResult{}

	// PHADAM logic from TORDAM.FOR
	powfac := 80.0
	rana := dc.rng.Float64()
	hit := 0.0
	phit := float64(blastAmt)

	// Shields up halves powfac for ships, always halved for bases
	if target.Type != "Base" && target.ShieldsUpDown && target.Shields > 0 {
		powfac = powfac / 2.0
	}
	if target.Type == "Base" {
		powfac = powfac / 2.0
	}

	// Hit strength is inversely proportional to distance from the target.
	// hit = pwr(0.9 + 0.02 * ran(0), id)
	hit = math.Pow(0.9+0.02*dc.rng.Float64(), float64(phaserRange))

	// System degradation: phaser/computer damage reduces effectiveness
	// DECWAR PHADAM (TORDAM.FOR:18993-18994)
	// Binary threshold: any damage > 0 applies 0.8x multiplier
	if attacker.PhasersDamage > 0 || attacker.ComputerDamage > 0 {
		hit = hit * 0.8
	}

	var hita float64
	var shieldStrength float64
	var shieldReduction float64

	if target.Type == "Base" {
		// Base shield logic: shields nullify based on percent strength
		if target.Shields > 0 {
			hita = hit
			shieldStrength = float64(target.Shields) / float64(InitialShieldValue) * 1000.0
			hit = (1000.0 - shieldStrength) * hita * 0.001
			shieldReduction = (hita*powfac*phit*math.Max(shieldStrength*0.001, 0.1) + 10.0) * 0.03
			result.ShieldDamage = int(shieldReduction)
			if target.Shields-int(shieldReduction) < 0 {
				result.ShieldsDown = true
			}
		}
		hita = hit * powfac * phit
	} else {
		// Ship/Planet shield logic: shields nullify based on percent strength.
		// If shields are up, the shield's current percent strength determines how much
		// of the incoming hit is nullified. If shields are down, 100% gets through.
		if target.ShieldsUpDown && target.Shields > 0 {
			hita = hit
			shieldStrength = float64(target.Shields) / float64(InitialShieldValue) * 1000.0
			hit = (1000.0 - shieldStrength) * hita * 0.001
			shieldReduction = (hita*powfac*phit*math.Max(shieldStrength*0.001, 0.1) + 10.0) * 0.03
			result.ShieldDamage = int(shieldReduction)
			if target.Shields-int(shieldReduction) < 0 {
				result.ShieldsDown = true
			}
		}
		hita = hit * powfac * phit
	}

	ihita := int(hita)

	// Critical hit logic
	critCheck := hita * (rana + 0.1)
	if critCheck >= 1700.0 {
		result.CriticalHit = true
		if target.Type == "Base" {
			// 1 in 5 chance for extra damage and possible destruction
			if dc.rng.Intn(5) == 4 {
				extraDamage := 50 + dc.rng.Intn(100)
				result.ShieldDamage += extraDamage
				if dc.rng.Intn(10) == 9 || target.Shields-result.ShieldDamage <= 0 {
					result.TargetDestroyed = true
				}
			}
		} else {
			// Ship: damage random device
			hita = hita / 2.0
			result.CriticalDevice = dc.rng.Intn(9) + 1 // device 1-9
			result.CriticalDamageAmt = int(hita)
			// Add random variance
			hita = hita + (dc.rng.Float64()-0.5)*1000.0
			ihita = int(hita)
		}
	}

	result.Damage = ihita

	// Destruction logic
	if target.Type != "Base" {
		result.TargetDestroyed = target.TotalShipDamage+result.Damage >= CriticalShipDamage || target.ShipEnergy-result.Damage/10 <= 0
	} else {
		result.TargetDestroyed = target.ShipEnergy <= 0
	}
	return result
}

// CalculateNovaDamage calculates nova damage without applying it.
// Takes into account range, target type, shields, and critical hit chances.
func (dc *DamageCalculator) CalculateNovaDamage(target *Object, attacker *Object, blastAmt int, phaserRange int) DamageResult {

	result := DamageResult{}

	powfac := 80.0
	phit := float64(blastAmt)

	// Reduce powfac if target has shields up
	if target.ShieldsUpDown && target.Shields > 0 {
		powfac = powfac / 2.0
	}

	// Calculate initial hit using power function with range - ensure positive hit value
	hit := math.Pow(0.9+0.1*dc.rng.Float64(), float64(phaserRange))

	var hita float64

	// Branch based on target type
	if target.Type == "Base" {
		// Base damage calculation
		if target.ShieldsUpDown && target.Shields > 0 {
			hita = hit
			baseShieldStrength := float64(target.Shields) / float64(InitialShieldValue) * 1000.0
			hit = (1000.0 - baseShieldStrength) * hita * 0.001

			// Calculate base shield reduction
			shieldReduction := (hita*powfac*phit*math.Max(baseShieldStrength*0.001, 0.1) + 10.0) * 0.03
			result.ShieldDamage = int(shieldReduction)

			// Final damage calculation
			hita = hit * powfac * phit

		} else {
			// Shields down: full damage
			hita = hit * powfac * phit

		}
	} else {
		// Ship, planet and star damage calculation
		if target.ShieldsUpDown && target.Shields > 0 {
			// Ship with shields up
			hita = hit
			shipShieldStrength := float64(target.Shields) / float64(InitialShieldValue) * 1000.0
			hit = (1000.0 - shipShieldStrength) * hita * 0.001

			// Calculate ship shield reduction
			shieldReduction := (hita*powfac*phit*math.Max(shipShieldStrength*0.001, 0.1) + 10.0) * 0.03
			result.ShieldDamage = int(shieldReduction)

		}
		// Final damage calculation
		hita = hit * powfac * phit
	}

	ihita := int(hita)

	// Critical hit check
	rana := dc.rng.Float64()
	critCheck := hita * (rana + 0.1)

	if critCheck >= 1700.0 {
		result.CriticalHit = true

		if target.Type == "Base" {
			// Base critical hit (1 in 5 chance of destruction)
			destructionRoll := dc.rng.Intn(5)

			if destructionRoll == 4 {
				extraDamage := 50 + dc.rng.Intn(100)
				result.ShieldDamage += extraDamage
				finalRoll := dc.rng.Intn(10)

				if finalRoll == 9 || target.Shields-result.ShieldDamage <= 0 {
					result.TargetDestroyed = true

				}
			}
		} else {
			// Ship critical hit - damage random device
			hita = hita / 2.0
			critDamage := hita / 100

			result.CriticalDevice = dc.rng.Intn(9) + 1 // Pick device 1-9
			result.CriticalDamageAmt = int(critDamage)

			// Add random variance to damage
			randomVariance := (dc.rng.Float64() - 0.5) * 1000.0
			hita = hita + randomVariance
			ihita = int(hita)
		}
	}

	result.Damage = ihita

	// Check if shields would go down
	result.ShieldsDown = target.Shields-result.ShieldDamage <= 0

	// Check for destruction
	if target.Type != "Base" {
		result.TargetDestroyed = target.TotalShipDamage+result.Damage >= CriticalShipDamage || target.ShipEnergy-result.Damage/10 <= 0
	} else {
		result.TargetDestroyed = target.ShipEnergy <= 0
	}

	return result
}

// ApplyDamageResult applies the calculated damage to the target object.
// This is the only function that modifies game state in the damage system.
func (i *Interpreter) ApplyDamageResult(targetIdx int, result DamageResult) {
	target := i.objects[targetIdx]

	// Apply shield damage: if target shields are up, hit damage decreases the
	// shield energy reserve (maximum of 2,500 units / 25,000 internal scale)
	target.Shields = int(math.Max(float64(target.Shields-result.ShieldDamage), 0))

	// Apply critical device damage
	if result.CriticalDevice > 0 && result.CriticalDamageAmt > 0 {
		switch result.CriticalDevice {
		case 1: // Shields
			target.ShieldsDamage += result.CriticalDamageAmt
			target.ShieldsUpDown = false
		case 2: // Warp Engines
			target.WarpEnginesDamage += result.CriticalDamageAmt
		case 3: // Impulse Engines
			target.ImpulseEnginesDamage += result.CriticalDamageAmt
		case 4: // Torpedo Tubes
			target.TorpedoTubeDamage += result.CriticalDamageAmt
		case 5: // Phasers
			target.PhasersDamage += result.CriticalDamageAmt
		case 6: // Computer
			target.ComputerDamage += result.CriticalDamageAmt
		case 7: // Life Support
			target.LifeSupportDamage += result.CriticalDamageAmt
		case 8: // Radio
			target.RadioDamage += result.CriticalDamageAmt
		case 9: // Tractor
			target.TractorDamage += result.CriticalDamageAmt
		}
	}

	// Apply structural damage. result.Damage is at 100x display scale.
	// TotalShipDamage is stored at 100x display scale (divide by 100.0 for display).
	// Shield damage does NOT contribute to structural damage — it only reduces shield reserves.
	target.TotalShipDamage += result.Damage

	// Reduce ship energy by the hit damage. ShipEnergy is at 10x display scale,
	// result.Damage is at 100x display scale, so divide by 10 to convert.
	// In original DECWAR, hits reduce both structural damage AND ship energy.
	// Ships can be destroyed by reaching 2,500 structural damage OR depleting energy to 0.
	if target.Type == "Ship" {
		target.ShipEnergy -= result.Damage / 10
		if target.ShipEnergy < 0 {
			target.ShipEnergy = 0
		}
	}

	// Turn shields down if shield strength <= 0
	if result.ShieldsDown {
		target.ShieldsUpDown = false
	}

	// Handle destruction and condition setting.
	// destructionFlag is managed exclusively via atomic.CompareAndSwapUint32 in
	// DoDamage/DestroyObject — do not touch it here.
	if result.TargetDestroyed {
		target.ShipEnergy = 0
		target.Condition = "Destroyed"

		if target.Type == "Ship" {
			// Clean up tractor beam relationships when ship is destroyed
			i.cleanupShipTractorBeams(target)
		}
	} else {
		// Not destroyed — set condition to RED for non-base targets
		if target.Type != "Base" {
			target.Condition = "RED"
		}
		// Reset atomic destruction flag for objects that recover (e.g. planets
		// whose damage is administratively reversed).
		if target.Type == "Planet" {
			atomic.StoreUint32(&target.destructionFlag, 0)
		}
	}
}

// DoDamage calculates and applies damage for all interactions (torpedoes and phasers).
// This is the main entry point that coordinates the damage calculation system.
func (i *Interpreter) DoDamage(iwhat string, targetIdx int, attackerIdx int, blastAmt int) (*CombatEvent, error) {
	var maxphaserBlast float64 = 500.0 //From decwar - hsn
	var minPhaserBlast float64 = 50.0  // Minimum phaser energy per spec

	// Defensive checks for index bounds
	if targetIdx < 0 || targetIdx >= len(i.objects) {
		return nil, fmt.Errorf("DoDamage: targetIdx %d out of bounds (len=%d)", targetIdx, len(i.objects))
	}
	if attackerIdx < 0 || attackerIdx >= len(i.objects) {
		return nil, fmt.Errorf("DoDamage: attackerIdx %d out of bounds (len=%d)", attackerIdx, len(i.objects))
	}

	// Early exit if target already destroyed (no energy or damage > 2500)
	if i.objects[targetIdx].ShipEnergy <= 0 || i.objects[targetIdx].TotalShipDamage >= CriticalShipDamage {
		evt := &CombatEvent{
			Galaxy:      i.objects[targetIdx].Galaxy,
			AttackerIdx: attackerIdx,
			TargetIdx:   targetIdx,
			Weapon:      iwhat,
			Damage:      0,
			Message:     "target already destroyed",
		}
		return evt, nil
	}

	// Determine distance to object (if not, message "out of range")
	phaserRange := max(AbsInt(i.objects[targetIdx].LocationX-i.objects[attackerIdx].LocationX), AbsInt(i.objects[targetIdx].LocationY-i.objects[attackerIdx].LocationY))

	if phaserRange > MaxRange {
		evt := &CombatEvent{
			Galaxy:      i.objects[targetIdx].Galaxy,
			AttackerIdx: attackerIdx,
			TargetIdx:   targetIdx,
			Weapon:      iwhat,
			Damage:      0,
			Message:     "Target out of range",
		}
		return evt, nil
	}

	// If requested phaser amount is improper (out of range)
	// For ships: enforce 50-500 unit range (500-5000 internal scale)
	// For bases/planets: only enforce maximum
	if iwhat == "Phaser" {
		isShipAttacker := i.objects[attackerIdx].Type == "Ship"
		if isShipAttacker && (blastAmt < int(minPhaserBlast)*10 || blastAmt > int(maxphaserBlast)*10) {
			evt := &CombatEvent{
				Galaxy:      i.objects[targetIdx].Galaxy,
				AttackerIdx: attackerIdx,
				TargetIdx:   targetIdx,
				Weapon:      iwhat,
				Damage:      0,
				Message:     "Weapons Officer:  Improper energy consumption for phaser hit, sir.",
			}
			return evt, nil
		} else if !isShipAttacker && blastAmt < 1 {
			evt := &CombatEvent{
				Galaxy:      i.objects[targetIdx].Galaxy,
				AttackerIdx: attackerIdx,
				TargetIdx:   targetIdx,
				Weapon:      iwhat,
				Damage:      0,
				Message:     "Weapons Officer:  Improper energy consumption for phaser hit, sir.",
			}
			return evt, nil
		}
	}

	// Are phasers broken?
	if iwhat == "Phaser" && i.objects[attackerIdx].PhasersDamage/100 > CriticalDamage {
		evt := &CombatEvent{
			Galaxy:      i.objects[targetIdx].Galaxy,
			AttackerIdx: attackerIdx,
			TargetIdx:   targetIdx,
			Weapon:      iwhat,
			Damage:      0,
			Message:     "Phasers critically damaged.",
		}
		return evt, nil
	}

	// Create damage calculator using this galaxy's per-instance RNG (no mutex needed).
	galaxyID := i.objects[targetIdx].Galaxy
	i.galaxiesMutex.RLock()
	gal := i.galaxies[galaxyID]
	i.galaxiesMutex.RUnlock()
	var calcRng *rand.Rand
	if gal != nil {
		calcRng = gal.rng
	} else {
		calcRng = newSeededRand()
	}
	calculator := NewDamageCalculator(calcRng)
	var result DamageResult

	if iwhat == "Torpedo" {
		result = calculator.CalculateTorpedoDamage(i.objects[targetIdx])
	} else if iwhat == "Phaser" {
		result = calculator.CalculatePhaserDamage(i.objects[targetIdx], i.objects[attackerIdx], blastAmt, phaserRange)
	} else if iwhat == "Nova" {
		result = calculator.CalculateNovaDamage(i.objects[targetIdx], i.objects[attackerIdx], blastAmt, phaserRange)
	}

	// Handle deflection case
	if result.Deflected {
		i.objects[targetIdx].Shields = int(math.Max(float64(i.objects[targetIdx].Shields-result.ShieldDamage), 0))
		evt := &CombatEvent{
			Galaxy:      i.objects[targetIdx].Galaxy,
			AttackerIdx: attackerIdx,
			TargetIdx:   targetIdx,
			Weapon:      iwhat,
			Damage:      0,
			Message:     result.Message,
		}
		return evt, nil
	}

	// Apply the damage result under spatial index lock to prevent concurrent modification
	i.spatialIndexMutex.Lock()
	i.ApplyDamageResult(targetIdx, result)
	i.spatialIndexMutex.Unlock()

	// Set destruction message if destroyed for notification logic.
	// DestroyObject performs atomic CAS so only one path emits the message.
	msg := "... formatted later ..."
	if result.TargetDestroyed {
		if atomic.CompareAndSwapUint32(&i.objects[targetIdx].destructionFlag, 0, 1) {
			// Won the CAS race: signal callers that destruction messaging is our job.
			msg = "destroyed"
		}
	}

	evt := &CombatEvent{
		Galaxy:            i.objects[targetIdx].Galaxy,
		AttackerIdx:       attackerIdx,
		TargetIdx:         targetIdx,
		Weapon:            iwhat,
		Damage:            result.Damage,
		Message:           msg,
		CriticalHit:       result.CriticalHit,
		CriticalDevice:    result.CriticalDevice,
		CriticalDamageAmt: result.CriticalDamageAmt,
	}
	return evt, nil
}

// NewInterpreter creates a new interpreter with predefined commands
func NewInterpreter(programStart time.Time, connections *sync.Map) *Interpreter {
	i := &Interpreter{
		pregameCommands:      make(map[string]Command),
		gowarsCommands:       make(map[string]Command),
		programStart:         programStart,
		connections:          connections,
		writers:              &sync.Map{},
		writerMutexs:         &sync.Map{},
		objectsByLocation:    make(map[uint16]map[string]*Object),
		objectsByType:        make(map[uint16]map[string][]*Object),
		shipsByGalaxyAndName: make(map[uint16]map[string]*Object),
		galaxies:             make(map[uint16]*Galaxy),
		galaxyInitOnce:       make(map[uint16]*sync.Once),
		galaxyTracker:        make(map[uint16]GalaxyTracker),
		lastSide:             "empire", // Start with empire so first ship is federation
		reservedWords:        make(map[string]struct{}),
		TaskQueue:            make(chan *GameTask, 1000), // Buffered channel for game tasks
		stateEngineRunning:   false,
		shutdown:             make(chan struct{}),
		destroyedCooldowns:   make(map[string]map[uint16]time.Time),
		instanceID:           newSeededRand().Int(),
		galaxyParams:         make(map[uint16]GalaxyParams),
	}

	params := getDefaultGalaxyParams()
	i.resetAndReinitializeGalaxy(0, params) // Initialize galaxy 0 atomically
	i.registerCommands()

	// Populate reservedWords
	reserved := []string{
		"quit", "time", "news", "gripe", "users", "activate", "chat", "summary", "help", "?",
		"list", "neutral", "friendly", "enemy", "closest", "ships", "bases", "planets", "human", "empire", "targets", "captured", "move",
	}
	for _, word := range reserved {
		i.reservedWords[strings.ToLower(word)] = struct{}{}
	}

	// Start galaxy cleanup goroutine
	go i.cleanupInactiveGalaxies()

	// Start the atomic state engine
	//	go i.StartStateEngine()

	// Start the game end checker goroutine
	go i.gameender()

	return i
}

// formatLocationKey creates a string key for coordinates
func (i *Interpreter) getOrCreateGalaxy(galaxyID uint16) *Galaxy {
	// Get or create the sync.Once for this galaxyID
	i.galaxyInitOnceMutex.Lock()
	once, exists := i.galaxyInitOnce[galaxyID]
	if !exists {
		once = &sync.Once{}
		i.galaxyInitOnce[galaxyID] = once
	}
	i.galaxyInitOnceMutex.Unlock()

	// Only one goroutine will initialize the galaxy
	once.Do(func() {
		i.galaxiesMutex.Lock()
		defer i.galaxiesMutex.Unlock()
		if _, exists := i.galaxies[galaxyID]; !exists {
			galaxy := &Galaxy{
				ID:           galaxyID,
				CommandQueue: make(chan *GameTask, 100),
				RobotQueue:   make(chan robotTask, 1),
				LastActive:   time.Now(),
				Done:         make(chan struct{}),
				syncDone:     make(chan struct{}),
				rng:          newSeededRand(),
			}

			// Prefer any stored custom params for this galaxy; fall back to defaults
			i.galaxyParamsMutex.RLock()
			params, ok := i.galaxyParams[galaxyID]
			i.galaxyParamsMutex.RUnlock()
			if !ok {
				params = getDefaultGalaxyParams()
			}

			i.initializeObjectsWithParams(galaxyID, params)
			i.galaxies[galaxyID] = galaxy // Insert only after full initialization
			go i.processGalaxyCommands(galaxy)
			go i.processGalaxyRobots(galaxy)
		}
	})

	i.galaxiesMutex.RLock()
	galaxy := i.galaxies[galaxyID]
	i.galaxiesMutex.RUnlock()
	return galaxy
}

// resetAndReinitializeGalaxy atomically removes all objects for a galaxy and re-initializes it
func (i *Interpreter) resetAndReinitializeGalaxy(galaxyID uint16, params GalaxyParams) {
	// Signal the old galaxy's command processor to stop (if it exists)
	i.galaxiesMutex.RLock()
	if oldGalaxy, exists := i.galaxies[galaxyID]; exists && oldGalaxy.Done != nil {
		select {
		case <-oldGalaxy.Done:
			// Already closed
		default:
			close(oldGalaxy.Done)
		}
	}
	i.galaxiesMutex.RUnlock()

	// Remove all objects for this galaxy (including ships, bases, planets, etc.)
	i.spatialIndexMutex.Lock()
	var remainingObjects []*Object
	for _, obj := range i.objects {
		if obj == nil {
			log.Printf("WARNING: nil object found in i.objects during galaxy reset!")
			continue
		}
		if obj.Galaxy != galaxyID {
			remainingObjects = append(remainingObjects, obj)
		}
	}
	i.objects = remainingObjects
	i.spatialIndexMutex.Unlock()

	// Remove the galaxy struct from i.galaxies
	i.galaxiesMutex.Lock()
	delete(i.galaxies, galaxyID)
	i.galaxiesMutex.Unlock()

	// Reset the sync.Once for this galaxy so it can be re-initialized
	i.galaxyInitOnceMutex.Lock()
	i.galaxyInitOnce[galaxyID] = &sync.Once{}
	i.galaxyInitOnceMutex.Unlock()

	// Store the custom params for this galaxy so initialization can use them
	i.galaxyParamsMutex.Lock()
	i.galaxyParams[galaxyID] = params
	i.galaxyParamsMutex.Unlock()

	// Now call getOrCreateGalaxy, which will re-initialize
	i.getOrCreateGalaxy(galaxyID)
}

// processGalaxyRobots is the per-galaxy robot worker.  It runs in its own
// goroutine, started once alongside processGalaxyCommands.  It waits for
// robotTask messages, re-acquires galaxy.Mutex, and calls robotsUnlocked —
// exactly as the old inline call did, but without blocking the CommandQueue.
//
// Because RobotQueue has capacity 1 and senders use a non-blocking select,
// rapid human commands coalesce: if a robot pass is already in flight, the
// next trigger is queued; if a pass is already queued, the new trigger is
// silently dropped (the already-queued pass will see up-to-date state when
// it eventually runs).
func (i *Interpreter) processGalaxyRobots(galaxy *Galaxy) {
	log.Printf("Galaxy %d robot processor started", galaxy.ID)
	for {
		select {
		case rt := <-galaxy.RobotQueue:
			// Re-acquire the galaxy mutex so robotsUnlocked sees a consistent
			// snapshot and its writes don't race with concurrent commands.
			galaxy.Mutex.Lock()
			log.Printf("Running robots (async) for galaxy %d, caller side: %s", rt.galaxy, rt.callerSide)
			i.robotsUnlocked(rt.galaxy, rt.callerSide)

			// Destruction phase — same as the old inline block.
			i.spatialIndexMutex.RLock()
			for _, obj := range i.objects {
				if obj.Galaxy != rt.galaxy {
					continue
				}
				if obj.Condition == "Destroyed" {
					i.DestroyObject(obj, rt.galaxy)
				}
			}
			i.spatialIndexMutex.RUnlock()

			// Broadcast world state after robot actions settle.
			i.broadcastWorldState(rt.galaxy)
			i.syncShipStateWithinGalaxy(rt.galaxy)

			galaxy.Mutex.Unlock()

		case <-galaxy.Done:
			log.Printf("Galaxy %d robot processor shutting down (galaxy done)", galaxy.ID)
			return

		case <-i.shutdown:
			log.Printf("Galaxy %d robot processor shutting down (global shutdown)", galaxy.ID)
			return
		}
	}
}

func (i *Interpreter) processGalaxyCommands(galaxy *Galaxy) {
	log.Printf("Galaxy %d command processor started", galaxy.ID)
	for {
		select {
		case task := <-galaxy.CommandQueue:
			log.Printf("Processing task: %s from player %s in galaxy %d (state-changing: %v)",
				task.Command, task.PlayerID, task.Galaxy, task.IsStateChanging)

			// Lock the galaxy for processing
			galaxy.Mutex.Lock()

			// --- ATOMIC START ---
			// 1. Process the Player's command
			result := i.executeCommand(task)

			// 2. Broadcast updates to everyone (if needed)
			// 2. Broadcast updates to everyone (if needed)
			// Note: galaxy 0 is a valid game galaxy; use >= 0 not > 0
			i.broadcastWorldState(task.Galaxy)

			if task.IsStateChanging {
				// 3. Ensure state is fully synchronized before handing off to robots.
				i.syncShipStateWithinGalaxy(task.Galaxy)

				// 4. Re-read the galaxy from the live connection, not the stale task snapshot.
				liveGalaxy := task.Galaxy
				if info, ok := i.connections.Load(task.Conn); ok {
					liveGalaxy = info.(ConnectionInfo).Galaxy
				}
				callerSide := i.getPlayerSide(task.PlayerID, liveGalaxy)

				// 5. Fire the robot pass asynchronously.  Use a non-blocking send so
				//    that a slow robot pass already in flight (or already queued) never
				//    stalls the human command loop.
				log.Printf("Enqueuing robot task for galaxy %d, caller side: %s", liveGalaxy, callerSide)
				select {
				case galaxy.RobotQueue <- robotTask{galaxy: liveGalaxy, callerSide: callerSide}:
				default:
					// A robot pass is already queued; the queued pass will see
					// current state when it runs, so dropping this trigger is safe.
					log.Printf("Galaxy %d robot queue full, coalescing robot trigger", liveGalaxy)
				}
			}

			galaxy.LastActive = time.Now()
			// Signal all SyncShipState waiters that this batch is complete.
			// Must be called while galaxy.Mutex is still held so that any waiter
			// that immediately requeues a task cannot race past us.
			galaxy.signalBatchDone()
			galaxy.Mutex.Unlock()

			// 7. Tell the player the result (after complete atomic block)
			start := time.Now()
			task.Response <- result
			elapsed := time.Since(start).Nanoseconds()
			log.Printf("Task completed for player %s: %s %v in %d ns", task.PlayerID, task.Command, task.Args, elapsed)
			// --- ATOMIC END ---

		case <-galaxy.Done:
			log.Printf("Galaxy %d command processor shutting down (galaxy done)", galaxy.ID)
			return

		case <-i.shutdown:
			log.Printf("Galaxy %d command processor shutting down (global shutdown)", galaxy.ID)
			return
		}
	}
}

func formatLocationKey(x, y int) string {
	return fmt.Sprintf("%d,%d", x, y)
}

// addObjectToSpatialIndex adds an object to all spatial indexes
func (i *Interpreter) addObjectToSpatialIndex(obj *Object) {
	i.spatialIndexMutex.Lock()
	defer i.spatialIndexMutex.Unlock()
	i.addObjectToSpatialIndexNoLock(obj)
}

// Internal version: does not lock mutex, for use when mutex is already held

// Internal version: does not lock
func (i *Interpreter) addObjectToSpatialIndexNoLock(obj *Object) {
	galaxy := obj.Galaxy
	log.Printf("Adding object to spatial index: Galaxy=%d, Type=%s, Name=%s, Location=(%d, %d)", galaxy, obj.Type, obj.Name, obj.LocationX, obj.LocationY)

	// Initialize galaxy maps if needed
	if i.objectsByLocation[galaxy] == nil {
		i.objectsByLocation[galaxy] = make(map[string]*Object)
	}
	if i.objectsByType[galaxy] == nil {
		i.objectsByType[galaxy] = make(map[string][]*Object)
	}
	if i.shipsByGalaxyAndName[galaxy] == nil {
		i.shipsByGalaxyAndName[galaxy] = make(map[string]*Object)
	}

	// Add to location index
	locKey := formatLocationKey(obj.LocationX, obj.LocationY)
	i.objectsByLocation[galaxy][locKey] = obj
	log.Printf("Added to location index: Galaxy=%d, LocationKey=%s", galaxy, locKey)

	// Add to type index
	i.objectsByType[galaxy][obj.Type] = append(i.objectsByType[galaxy][obj.Type], obj)
	log.Printf("Added to type index: Galaxy=%d, Type=%s", galaxy, obj.Type)

	// Add to ship name index if it's a ship
	if obj.Type == "Ship" && obj.Name != "" {
		i.shipsByGalaxyAndName[galaxy][obj.Name] = obj
		log.Printf("Added to ship name index: Galaxy=%d, ShipName=%s", galaxy, obj.Name)
	}
}

// removeObjectFromSpatialIndex removes an object from all spatial indexes
func (i *Interpreter) removeObjectFromSpatialIndex(obj *Object) {
	i.spatialIndexMutex.Lock()
	defer i.spatialIndexMutex.Unlock()
	i.removeObjectFromSpatialIndexNoLock(obj)
}

// Internal version: does not lock
func (i *Interpreter) removeObjectFromSpatialIndexNoLock(obj *Object) {
	galaxy := obj.Galaxy

	if i.objectsByLocation[galaxy] == nil {
		log.Printf("removeObjectFromSpatialIndexNoLock: Galaxy %d does not exist in objectsByLocation", galaxy)
		return
	}

	// Remove from location index
	locKey := formatLocationKey(obj.LocationX, obj.LocationY)
	log.Printf("removeObjectFromSpatialIndexNoLock: Removing object at location %s in galaxy %d", locKey, galaxy)
	delete(i.objectsByLocation[galaxy], locKey)

	// Remove from type index
	if typeSlice, exists := i.objectsByType[galaxy][obj.Type]; exists {
		for idx, o := range typeSlice {
			if o == obj {
				// Remove by replacing with last element and truncating
				log.Printf("removeObjectFromSpatialIndexNoLock: Removing object of type %s at index %d in galaxy %d", obj.Type, idx, galaxy)
				typeSlice[idx] = typeSlice[len(typeSlice)-1]
				i.objectsByType[galaxy][obj.Type] = typeSlice[:len(typeSlice)-1]
				break
			}
		}
	}

	// Remove from ship name index if it's a ship
	if obj.Type == "Ship" && obj.Name != "" {
		log.Printf("removeObjectFromSpatialIndexNoLock: Removing ship %s from galaxy %d", obj.Name, galaxy)
		delete(i.shipsByGalaxyAndName[galaxy], obj.Name)
	}
}

// rebuildSpatialIndexesLocked rebuilds all spatial indexes from the objects slice.
// Caller MUST already hold spatialIndexMutex (write lock).
func (i *Interpreter) rebuildSpatialIndexesLocked() {
	// Clear existing indexes
	i.objectsByLocation = make(map[uint16]map[string]*Object)
	i.objectsByType = make(map[uint16]map[string][]*Object)
	i.shipsByGalaxyAndName = make(map[uint16]map[string]*Object)

	// Rebuild from objects slice - don't call addObjectToSpatialIndex to avoid double locking
	for _, obj := range i.objects {
		galaxy := obj.Galaxy

		// Initialize galaxy maps if needed
		if i.objectsByLocation[galaxy] == nil {
			i.objectsByLocation[galaxy] = make(map[string]*Object)
		}
		if i.objectsByType[galaxy] == nil {
			i.objectsByType[galaxy] = make(map[string][]*Object)
		}
		if i.shipsByGalaxyAndName[galaxy] == nil {
			i.shipsByGalaxyAndName[galaxy] = make(map[string]*Object)
		}

		// Add to location index
		locKey := formatLocationKey(obj.LocationX, obj.LocationY)
		i.objectsByLocation[galaxy][locKey] = obj

		// Add to type index
		i.objectsByType[galaxy][obj.Type] = append(i.objectsByType[galaxy][obj.Type], obj)

		// Add to ship name index if it's a ship
		if obj.Type == "Ship" && obj.Name != "" {
			i.shipsByGalaxyAndName[galaxy][obj.Name] = obj
		}
	}
}

// rebuildSpatialIndexes rebuilds all spatial indexes from the objects slice.
// Acquires spatialIndexMutex internally.
func (i *Interpreter) rebuildSpatialIndexes() {
	i.spatialIndexMutex.Lock()
	defer i.spatialIndexMutex.Unlock()
	i.rebuildSpatialIndexesLocked()
}

// getObjectAtLocation returns the object at the specified coordinates
// getObjectAtLocationLocked returns the object at the given location.
// Caller MUST already hold spatialIndexMutex (read or write lock).
func (i *Interpreter) getObjectAtLocationLocked(galaxy uint16, x, y int) *Object {
	if galaxyMap, exists := i.objectsByLocation[galaxy]; exists {
		locKey := formatLocationKey(x, y)
		return galaxyMap[locKey]
	}
	return nil
}

// getObjectAtLocation returns the object at the given location.
// Acquires spatialIndexMutex (RLock) internally.
func (i *Interpreter) getObjectAtLocation(galaxy uint16, x, y int) *Object {
	i.spatialIndexMutex.RLock()
	defer i.spatialIndexMutex.RUnlock()
	return i.getObjectAtLocationLocked(galaxy, x, y)
}

// getObjectsByTypeLocked returns all objects of the specified type in a galaxy.
// Caller MUST already hold spatialIndexMutex (read or write lock).
func (i *Interpreter) getObjectsByTypeLocked(galaxy uint16, objType string) []*Object {
	if galaxyMap, exists := i.objectsByType[galaxy]; exists {
		return galaxyMap[objType]
	}
	return nil
}

// getObjectsByType returns all objects of the specified type in a galaxy.
// Acquires spatialIndexMutex (RLock) internally.
func (i *Interpreter) getObjectsByType(galaxy uint16, objType string) []*Object {
	i.spatialIndexMutex.RLock()
	defer i.spatialIndexMutex.RUnlock()
	return i.getObjectsByTypeLocked(galaxy, objType)
}

// getShipByNameLocked returns a ship by name in the specified galaxy.
// Caller MUST already hold spatialIndexMutex (read or write lock).
func (i *Interpreter) getShipByNameLocked(galaxy uint16, shipName string) *Object {
	if galaxyMap, exists := i.shipsByGalaxyAndName[galaxy]; exists {
		return galaxyMap[shipName]
	}
	return nil
}

// getShipByName returns a ship by name in the specified galaxy.
// Acquires spatialIndexMutex (RLock) internally.
func (i *Interpreter) getShipByName(galaxy uint16, shipName string) *Object {
	i.spatialIndexMutex.RLock()
	defer i.spatialIndexMutex.RUnlock()
	return i.getShipByNameLocked(galaxy, shipName)
}

// updateObjectLocation updates an object's location and maintains spatial indexes
func (i *Interpreter) updateObjectLocation(obj *Object, newX, newY int) {
	i.spatialIndexMutex.Lock()
	defer i.spatialIndexMutex.Unlock()

	// Remove from all indexes at old location (no lock)
	log.Printf("Removing object %v from spatial index at old location (%d, %d)", obj.Name, obj.LocationX, obj.LocationY)
	i.removeObjectFromSpatialIndexNoLock(obj)

	// Update coordinates
	obj.LocationX = newX
	obj.LocationY = newY

	// Add to all indexes at new location (no lock)
	log.Printf("Adding object %v to spatial index at new location (%d, %d)", obj.Name, newX, newY)
	i.addObjectToSpatialIndexNoLock(obj)
}

// addObjectToObjects adds an object to the objects slice and spatial indexes
func (i *Interpreter) addObjectToObjects(obj Object) {
	i.spatialIndexMutex.Lock()
	defer i.spatialIndexMutex.Unlock()

	newObj := &Object{}
	*newObj = obj
	i.objects = append(i.objects, newObj)
	galaxy := newObj.Galaxy

	// Initialize galaxy maps if needed
	if i.objectsByLocation[galaxy] == nil {
		i.objectsByLocation[galaxy] = make(map[string]*Object)
	}
	if i.objectsByType[galaxy] == nil {
		i.objectsByType[galaxy] = make(map[string][]*Object)
	}
	if i.shipsByGalaxyAndName[galaxy] == nil {
		i.shipsByGalaxyAndName[galaxy] = make(map[string]*Object)
	}

	// Add to location index
	locKey := formatLocationKey(newObj.LocationX, newObj.LocationY)
	i.objectsByLocation[galaxy][locKey] = newObj

	// Add to type index
	i.objectsByType[galaxy][newObj.Type] = append(i.objectsByType[galaxy][newObj.Type], newObj)

	// Add to ship name index if it's a ship
	if newObj.Type == "Ship" && newObj.Name != "" {
		i.shipsByGalaxyAndName[galaxy][newObj.Name] = newObj
	}
}

// removeObjectByIndex removes an object at the specified index while maintaining spatial indexes
// removeObjectByIndexLocked removes an object by index from the objects slice and spatial indexes.
// Caller MUST already hold spatialIndexMutex (write lock).
// NOTE: Does NOT call refreshShipPointers — caller is responsible for that after releasing the lock,
// or by calling refreshShipPointersLocked if still under the lock.
func (i *Interpreter) removeObjectByIndexLocked(index int) {
	if index < 0 || index >= len(i.objects) {
		return
	}

	// Remove from spatial indexes first
	obj := i.objects[index]

	// Clean up tractor beam relationships if this is a ship
	if obj.Type == "Ship" {
		i.cleanupShipTractorBeams(obj)
	}
	galaxy := obj.Galaxy

	if i.objectsByLocation[galaxy] != nil {
		// Remove from location index
		locKey := formatLocationKey(obj.LocationX, obj.LocationY)
		delete(i.objectsByLocation[galaxy], locKey)

		// Remove from type index
		if typeSlice, exists := i.objectsByType[galaxy][obj.Type]; exists {
			for idx, o := range typeSlice {
				if o == obj {
					// Remove by replacing with last element and truncating
					typeSlice[idx] = typeSlice[len(typeSlice)-1]
					i.objectsByType[galaxy][obj.Type] = typeSlice[:len(typeSlice)-1]
					break
				}
			}
		}

		// Remove from ship name index if it's a ship
		if obj.Type == "Ship" && obj.Name != "" {
			delete(i.shipsByGalaxyAndName[galaxy], obj.Name)
		}
	}

	// Remove from objects slice
	i.objects = append(i.objects[:index], i.objects[index+1:]...)

	// Rebuild all pointers to ensure they point to the new slice position
	i.rebuildSpatialIndexesLocked()
}

// removeObjectByIndex removes an object by index from the objects slice and spatial indexes.
// Acquires spatialIndexMutex internally, then refreshes ship pointers after releasing it.
func (i *Interpreter) removeObjectByIndex(index int) {
	i.spatialIndexMutex.Lock()
	i.removeObjectByIndexLocked(index)
	i.spatialIndexMutex.Unlock()

	// Refresh all ship pointers after slice modification to prevent dangling pointers
	// Must be called after releasing the lock to avoid deadlock
	i.refreshShipPointers()
}

// startCleanupRoutine initializes a background process that periodically checks
// for and removes orphaned ships and orphaned sessions
func (i *Interpreter) startCleanupRoutine() {
	go func() {
		cleanupTicker := time.NewTicker(30 * time.Second)
		defer cleanupTicker.Stop()

		for range cleanupTicker.C {
			i.cleanupConnectionsAndShips()
		}
	}()
}

// cleanupConnectionsAndShips removes any connections that are no longer active
// and their associated ships.
//
// Lock contention is reduced by splitting work into phases:
//
//	Phase 1 (no spatial lock): Identify dead connections via keepalive, build active ship set.
//	Phase 2 (no spatial lock): Collect ship pointers from dead connections.
//	Phase 3 (spatial lock, defer): Perform all ship cleanups and orphan removal under one lock acquisition.
//	Phase 4 (no spatial lock): Delete connection entries from sync.Map.
//	Phase 5 (no spatial lock): Refresh ship pointers.
func (i *Interpreter) cleanupConnectionsAndShips() {
	// --- Phase 1: Identify dead connections (no spatial lock needed, sync.Map is concurrent-safe) ---
	var toRemove []net.Conn
	activeShips := make(map[string]struct{})

	i.connections.Range(func(key, value interface{}) bool {
		conn := key.(net.Conn)
		info := value.(ConnectionInfo)

		// Check if connection is still active
		if conn == nil {
			toRemove = append(toRemove, conn)
			return true
		}

		// Try to write a zero-byte keepalive packet
		_, err := conn.Write([]byte{})
		if err != nil {
			toRemove = append(toRemove, conn)
			return true
		}

		// This is an active connection, record its ship
		if info.Shipname != "" {
			shipKey := fmt.Sprintf("%s:%d", info.Shipname, info.Galaxy)
			activeShips[shipKey] = struct{}{}
		}
		return true
	})

	// --- Phase 2: Collect ship pointers from dead connections (no spatial lock needed) ---
	var shipsFromDeadConns []*Object
	for _, conn := range toRemove {
		if info, ok := i.connections.Load(conn); ok {
			connInfo := info.(ConnectionInfo)
			if connInfo.Ship != nil {
				shipsFromDeadConns = append(shipsFromDeadConns, connInfo.Ship)
			}
		}
	}

	// --- Phase 3: Lock and perform all ship cleanups + orphan detection ---
	func() {
		i.spatialIndexMutex.Lock()
		defer i.spatialIndexMutex.Unlock()

		// Clean up ships from dead connections
		for _, ship := range shipsFromDeadConns {
			i.cleanupShipNoLock(ship)
		}

		// Remove any ships that don't have active connections (orphans)
		for j := len(i.objects) - 1; j >= 0; j-- {
			obj := i.objects[j]
			if obj.Type == "Ship" && obj.Name != "" {
				// Skip non-player ships (like Romulans)
				if strings.HasPrefix(obj.Name, "Romulan") {
					continue
				}

				shipKey := fmt.Sprintf("%s:%d", obj.Name, obj.Galaxy)
				if _, exists := activeShips[shipKey]; !exists {
					// Ship has no active connection, remove it
					i.cleanupShipNoLock(obj)
				}
			}
		}
	}()

	// --- Phase 4: Clean up connection entries (no spatial lock needed) ---
	for _, conn := range toRemove {
		if info, ok := i.connections.Load(conn); ok {
			connInfo := info.(ConnectionInfo)
			connInfo.Lock()
			connInfo.Ship = nil
			connInfo.Shipname = "" // Also clear shipname for consistency
			connInfo.Unlock()
			i.connections.Store(conn, connInfo)
		}
		i.connections.Delete(conn)
	}

	// --- Phase 5: Refresh ship pointers for all connections after cleanup ---
	i.refreshShipPointers()
}

// adjustCount adjusts a base count by ±10%, ensuring it doesn't go below 0
func adjustCount(base int) int {
	factor := 0.9 + (newSeededRand().Float64() * 0.2) // 0.9 to 1.1
	adjusted := int(float64(base) * factor)
	if adjusted < 0 {
		return 0
	}
	return adjusted
}

// initializeObjects creates objects for a specified galaxy with ±10% variation
// GalaxyParams holds parameters for galaxy initialization
type GalaxyParams struct {
	DecwarMode           bool
	MaxSizeX             int
	MaxSizeY             int
	MaxRomulans          int
	MaxBlackHoles        int
	MaxNeutralPlanets    int
	MaxFederationPlanets int
	MaxEmpirePlanets     int
	MaxStars             int
	MaxBasesPerSide      int
}

// getDefaultGalaxyParams returns default galaxy parameters
func getDefaultGalaxyParams() GalaxyParams {
	return GalaxyParams{
		DecwarMode:           DecwarMode,
		MaxSizeX:             MaxSizeX,
		MaxSizeY:             MaxSizeY,
		MaxRomulans:          MaxRomulans,
		MaxBlackHoles:        MaxBlackHoles,
		MaxNeutralPlanets:    MaxNeutralPlanets,
		MaxFederationPlanets: MaxFederationPlanets,
		MaxEmpirePlanets:     MaxEmpirePlanets,
		MaxStars:             MaxStars,
		MaxBasesPerSide:      MaxBasesPerSide,
	}
}

// validateGalaxyBoundaries checks if coordinates are within galaxy boundaries
func (i *Interpreter) validateGalaxyBoundaries(galaxy uint16, x, y int) (bool, int, int) {
	galaxyMaxX := MaxSizeX
	galaxyMaxY := MaxSizeY

	i.trackerMutex.Lock()
	if tracker, exists := i.galaxyTracker[galaxy]; exists {
		if tracker.MaxSizeX > 0 {
			galaxyMaxX = tracker.MaxSizeX
		}
		if tracker.MaxSizeY > 0 {
			galaxyMaxY = tracker.MaxSizeY
		}
	}
	i.trackerMutex.Unlock()

	isValid := x >= 1 && x <= galaxyMaxX && y >= 1 && y <= galaxyMaxY
	return isValid, galaxyMaxX, galaxyMaxY
}

// validateGalaxyParams validates galaxy parameters
func validateGalaxyParams(galaxy uint16, params GalaxyParams) error {
	if galaxy >= MaxGalaxies {
		return fmt.Errorf("galaxy must be less than %d", MaxGalaxies)
	}

	if params.MaxSizeX <= 20 || params.MaxSizeX >= 100 {
		return fmt.Errorf("MaxSizeX must be > 20 and < 100")
	}

	if params.MaxSizeY <= 20 || params.MaxSizeY >= 100 {
		return fmt.Errorf("MaxSizeY must be > 20 and < 100")
	}

	if params.MaxRomulans < 0 || params.MaxRomulans >= 10000 {
		return fmt.Errorf("MaxRomulans must be >= 0 and < 10000")
	}

	if params.MaxBlackHoles < 0 || params.MaxBlackHoles >= 10000 {
		return fmt.Errorf("MaxBlackHoles must be >= 0 and < 10000")
	}

	if params.MaxNeutralPlanets < 0 || params.MaxNeutralPlanets >= 10000 {
		return fmt.Errorf("MaxNeutralPlanets must be >= 0 and < 10000")
	}

	if params.MaxFederationPlanets < 0 || params.MaxFederationPlanets >= 10000 {
		return fmt.Errorf("MaxFederationPlanets must be >= 0 and < 10000")
	}

	if params.MaxEmpirePlanets < 0 || params.MaxEmpirePlanets >= 10000 {
		return fmt.Errorf("MaxEmpirePlanets must be >= 0 and < 10000")
	}

	if params.MaxStars < 0 || params.MaxStars >= 10000 {
		return fmt.Errorf("MaxStars must be >= 0 and < 10000")
	}

	if params.MaxBasesPerSide < 0 || params.MaxBasesPerSide >= 10000 {
		return fmt.Errorf("MaxBasesPerSide must be >= 0 and < 10000")
	}

	totalObjects := params.MaxRomulans + params.MaxBlackHoles + params.MaxNeutralPlanets +
		params.MaxFederationPlanets + params.MaxEmpirePlanets + params.MaxStars + (params.MaxBasesPerSide * 2)

	if totalObjects < 0 || totalObjects >= 10000 {
		return fmt.Errorf("sum of all objects must be >= 0 and < 10000")
	}

	return nil
}

func (i *Interpreter) initializeObjects(galaxy uint16) {
	i.initializeObjectsWithParams(galaxy, getDefaultGalaxyParams())
}

func (i *Interpreter) initializeObjectsWithParams(galaxy uint16, params GalaxyParams) {
	// Use a freshly-seeded RNG for object placement; the galaxy's own rng is not
	// yet available here because this function runs before the Galaxy struct is
	// inserted into i.galaxies.
	localRng := newSeededRand()
	occupied := make(map[string]struct{}) // Track occupied x,y positions

	// Helper to add objects with adjusted counts
	seqMap := make(map[string]int) // Track sequence numbers for each object type
	addObjects := func(objType string, baseCount int, side string) {
		count := adjustCount(baseCount)
		for j := 0; j < count; j++ {
			var x, y int
			for {
				x = localRng.Intn(params.MaxSizeX) + 1
				y = localRng.Intn(params.MaxSizeY) + 1
				key := fmt.Sprintf("%d,%d", x, y)
				if _, exists := occupied[key]; !exists {
					occupied[key] = struct{}{}
					break
				}
			}
			shipName := ""
			if objType == "Ship" && side == "romulan" {
				if params.DecwarMode == true { //Only 1 Rom in decwar, allow more in gowar
					shipName = "Romulan"
				} else {
					shipName = "Romulan" + strconv.Itoa(j)
				}
			} else if objType == "Ship" {
				shipName = ""
			} else if objType == "Base" || objType == "Planet" || objType == "Star" || objType == "Black Hole" {
				if params.DecwarMode == false {
					seqMap[objType]++
					shipName = fmt.Sprintf("%s-%03d", objType, seqMap[objType])
				} else {
					shipName = objType
				}
			}
			// Set SeenByFed/SeenByEmp for bases
			seenByFed := false
			seenByEmp := false
			if objType == "Base" {
				if side == "federation" {
					seenByFed = true
				} else if side == "empire" {
					seenByEmp = true
				}
			}
			obj := &Object{
				Galaxy:    galaxy,
				Type:      objType,
				LocationX: x,
				LocationY: y,
				Side:      side,
				Name:      shipName, // Romulan ships named "Romulan"
				Shields:   InitialShieldValue,
				Condition: "Green",
				TorpedoTubes: func() int {
					if objType == "Ship" && side == "romulan" {
						return math.MaxInt
					}
					return 10
				}(),
				TorpedoTubeDamage:  0,
				PhasersDamage:      0,
				ComputerDamage:     0,
				LifeSupportDamage:  0,
				LifeSupportReserve: 5,
				RadioOnOff:         true,
				RadioDamage:        0,
				TractorOnOff:       false,
				TractorShip:        "",
				TractorDamage:      0,
				ShieldsUpDown: func() bool {
					if objType == "Planet" && side == "neutral" {
						return false
					}
					return true
				}(),
				ShipEnergy:        InitialShipEnergy,
				SeenByFed:         seenByFed,
				SeenByEmp:         seenByEmp,
				TotalShipDamage:   0,
				WarpEnginesDamage: 0,
				Builds:            0,
			}
			i.objects = append(i.objects, obj)
		}
	}

	addObjects("Star", params.MaxStars, "neutral")
	addObjects("Planet", params.MaxNeutralPlanets, "neutral")
	addObjects("Planet", params.MaxFederationPlanets, "federation")
	addObjects("Planet", params.MaxEmpirePlanets, "empire")
	addObjects("Base", params.MaxBasesPerSide, "federation")
	addObjects("Base", params.MaxBasesPerSide, "empire")
	addObjects("Black Hole", params.MaxBlackHoles, "neutral")
	if params.DecwarMode == true {
		addObjects("Ship", 1, "romulan")
	} else {
		addObjects("Ship", params.MaxRomulans, "romulan")
	}

	// Rebuild spatial indexes after adding all objects
	i.rebuildSpatialIndexes()

	// Update galaxy tracker
	i.trackerMutex.Lock()
	now := time.Now()
	i.galaxyTracker[galaxy] = GalaxyTracker{GalaxyStart: now, LastActive: now, MaxSizeX: params.MaxSizeX, MaxSizeY: params.MaxSizeY, MaxRomulans: params.MaxRomulans, DecwarMode: params.DecwarMode}
	i.trackerMutex.Unlock()
}

// cleanupInactiveGalaxies removes galaxies > 0 inactive for >10 minutes
func (i *Interpreter) cleanupInactiveGalaxies() {
	for {
		time.Sleep(1 * time.Minute) // Check every minute
		i.cleanupInactiveGalaxiesOnce()
	}
}

// cleanupInactiveGalaxiesOnce performs a single pass of inactive galaxy cleanup.
// Extracted so that defer-based unlocking works correctly (the outer loop never returns).
// Lock order: galaxiesMutex → spatialIndexMutex → trackerMutex (hierarchy enforced).
func (i *Interpreter) cleanupInactiveGalaxiesOnce() {
	now := time.Now()

	// Composite lock: galaxiesMutex, then spatialIndexMutex (correct hierarchy), then trackerMutex
	i.LockGalaxiesAndSpatialIndex()
	defer i.UnlockGalaxiesAndSpatialIndex()
	i.trackerMutex.Lock()
	defer i.trackerMutex.Unlock()

	for galaxy, tracker := range i.galaxyTracker {
		if galaxy == 0 { // Skip galaxy 0
			continue
		}
		// Check if any connection is in this galaxy
		active := false
		i.connections.Range(func(_, value interface{}) bool {
			info := value.(ConnectionInfo)
			if info.Galaxy == galaxy && info.Section == "gowars" {
				active = true
				return false // Stop iteration
			}
			return true
		})
		if !active && now.Sub(tracker.LastActive) > 10*time.Minute {
			// Signal the galaxy's command processor goroutine to stop
			if galaxyObj, exists := i.galaxies[galaxy]; exists && galaxyObj.Done != nil {
				select {
				case <-galaxyObj.Done:
					// Already closed
				default:
					close(galaxyObj.Done)
				}
			}
			// Reset the sync.Once so galaxy can be re-created if needed later
			i.galaxyInitOnceMutex.Lock()
			i.galaxyInitOnce[galaxy] = &sync.Once{}
			i.galaxyInitOnceMutex.Unlock()
			// Remove all objects in this galaxy using locked variant (spatialIndexMutex already held)
			for j := len(i.objects) - 1; j >= 0; j-- {
				if i.objects[j].Galaxy == galaxy {
					i.removeObjectByIndexLocked(j)
				}
			}
			// Rebuild spatial indexes after galaxy cleanup (spatialIndexMutex already held)
			i.rebuildSpatialIndexesLocked()
			// Delete galaxy from tracker
			delete(i.galaxyTracker, galaxy)
			// Delete galaxy from galaxies map (atomic deletion)
			delete(i.galaxies, galaxy)
		}
	}

	// Refresh ship pointers while still holding the lock
	i.refreshShipPointersLocked()
}

// checkGalaxyZeroBases checks if galaxy 0 has no bases for a side
func (i *Interpreter) checkGalaxyZeroBases() bool {

	fedBases := 0
	empBases := 0
	bases := i.getObjectsByType(0, "Base")
	if bases != nil {
		for _, obj := range bases {
			if obj.Side == "federation" {
				fedBases++
			} else if obj.Side == "empire" {
				empBases++
			}
		}
	}
	return fedBases == 0 || empBases == 0
}

// regenerateGalaxyZero resets galaxy 0 and moves all connections to pregame
func (i *Interpreter) regenerateGalaxyZero() {
	// Phase 1: Remove all objects in galaxy 0 under the spatial lock
	func() {
		i.spatialIndexMutex.Lock()
		defer i.spatialIndexMutex.Unlock()
		for j := len(i.objects) - 1; j >= 0; j-- {
			if i.objects[j].Galaxy == 0 {
				i.removeObjectByIndexLocked(j)
			}
		}
		i.refreshShipPointersLocked()
	}()

	// Phase 2: Regenerate galaxy 0 (resetAndReinitializeGalaxy acquires its own locks)
	params := getDefaultGalaxyParams()
	i.resetAndReinitializeGalaxy(0, params)

	// Phase 3: Move all connections to pregame and broadcast message
	i.connections.Range(func(key, value interface{}) bool {
		conn := key.(net.Conn)
		info := value.(ConnectionInfo)
		// Reset enteredTime when galaxy is regenerated and players return to pregame
		if info.Ship != nil {
			info.Ship.EnteredTime = nil
		}
		info.Section = "pregame"
		info.Shipname = ""
		info.Galaxy = 0
		info.Prompt = "" // Clear custom prompt when returning to pregame
		info.BaudRate = 0
		i.connections.Store(conn, info)
		if writerRaw, ok := i.writers.Load(conn); ok {
			writer := writerRaw.(*bufio.Writer)
			if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
				mutex := mutexRaw.(*sync.Mutex)
				mutex.Lock()
				fmt.Fprintf(writer, "\r\nThe war is over!\r\n")
				writer.Flush()
				mutex.Unlock()
			}
		}
		return true
	})
}

// getShipSide returns the side of the ship associated with the connection
func (i *Interpreter) getShipSide(conn net.Conn) (string, bool) {
	if info, ok := i.connections.Load(conn); ok {
		connInfo := info.(ConnectionInfo)
		if connInfo.Ship != nil {
			return connInfo.Ship.Side, true
		}
	}
	return "", false
}

// getShipLocation returns the location of the ship associated with the connection
func (i *Interpreter) getShipLocation(conn net.Conn) (int, int, bool) {
	if info, ok := i.connections.Load(conn); ok {
		connInfo := info.(ConnectionInfo)
		if connInfo.Ship != nil {
			return connInfo.Ship.LocationX, connInfo.Ship.LocationY, true
		}
	}
	return 0, 0, false
}

// refreshShipPointers updates all ship pointers after objects slice modifications
// This ensures ship pointers remain valid after slice reallocations
// refreshShipPointersLocked refreshes all ship pointers in connection info.
// Caller MUST already hold spatialIndexMutex (read or write lock).
func (i *Interpreter) refreshShipPointersLocked() {
	i.connections.Range(func(key, value interface{}) bool {
		conn := key.(net.Conn)
		connInfo := value.(ConnectionInfo)
		if connInfo.Shipname != "" {
			// Use spatial indexing for faster ship lookup (locked variant, no re-acquire)
			ship := i.getShipByNameLocked(connInfo.Galaxy, connInfo.Shipname)
			if ship != nil {
				connInfo.Ship = ship
				i.connections.Store(conn, connInfo)
			}
		}
		return true
	})
}

// refreshShipPointers refreshes all ship pointers in connection info.
// Acquires spatialIndexMutex (RLock) internally.
func (i *Interpreter) refreshShipPointers() {
	i.connections.Range(func(key, value interface{}) bool {
		conn := key.(net.Conn)
		connInfo := value.(ConnectionInfo)
		if connInfo.Shipname != "" {
			// Use spatial indexing for faster ship lookup
			ship := i.getShipByName(connInfo.Galaxy, connInfo.Shipname)
			if ship != nil {
				connInfo.Ship = ship
				i.connections.Store(conn, connInfo)
			}
		}
		return true
	})
}

func (i *Interpreter) getShipConnection(shipObj Object) net.Conn {
	if shipObj.Type != "Ship" {
		return nil
	}

	var foundConn net.Conn
	i.connections.Range(func(key, value interface{}) bool {
		conn := key.(net.Conn)
		connInfo := value.(ConnectionInfo)
		if connInfo.Shipname == shipObj.Name && connInfo.Galaxy == shipObj.Galaxy {
			foundConn = conn
			return false // Stop iteration
		}
		return true
	})
	return foundConn
}

// countConnections returns the number of active connections
func (i *Interpreter) countConnections() int {
	count := 0
	i.connections.Range(func(key, value interface{}) bool {
		count++
		return true
	})
	return count
}

// countConnectionsBySide returns the number of active connections for a specific side
func (i *Interpreter) countConnectionsBySide(side string) int {
	count := 0
	i.connections.Range(func(key, value interface{}) bool {
		if connInfo, ok := value.(*ConnectionInfo); ok {
			if connInfo.PreferredSide == side {
				count++
			}
		}
		return true
	})
	return count
}

// countTotalPlayers returns the total number of active players (federation + empire)
func (i *Interpreter) countTotalPlayers() int {
	return i.countConnectionsBySide("federation") + i.countConnectionsBySide("empire")
}

// checkEngineOverheating applies overheating checks for high-warp moves,
// mirroring decwar's logic exactly:
//
//	Warp 5: tran = iran(100); damage if tran > 90  (~9% chance)
//	Warp 6: tran = iran(100); damage if tran > 80  (~19% chance)
//	Damage amount: iran(4000) → 0-3999 units
//	"Engineering Officer:" prefix only on long output (decwar: oflg .eq. long)
//	Repair time message only on long/medium output (decwar: oflg .ne. short)
//
// Returns any warning/damage messages to append. Mutates ship damage in-place.
func checkEngineOverheating(ship *Object, warpDist int, scanType, outputState string, rng *rand.Rand) string {
	// Only warp 5 and 6 risk overheating
	var threshold int
	switch warpDist {
	case 5:
		threshold = 90 // damage if tran > 90 (~9% chance)
	case 6:
		threshold = 80 // damage if tran > 80 (~19% chance)
	default:
		return ""
	}

	// Emit overheating warning (decwar: engoff prefix only on long, move5L on long/medium, move5S on short)
	var result string
	if outputState == "long" {
		result += "Engineering Officer:  Captain, our engines are overheating!\n\r"
	} else if outputState == "medium" {
		result += "Captain, our engines are overheating!\n\r"
	} else {
		result += "Engines overheating.\n\r"
	}

	// Roll for damage: tran = iran(100), damage if tran > threshold
	tran := rng.Intn(100)
	if tran <= threshold {
		return result // no damage this time
	}

	// Damage occurs: randam = iran(4000), time = randam / 30
	dmg := rng.Intn(4000)
	ship.WarpEnginesDamage += dmg
	result += fmt.Sprintf("EEEEERRRRRROOOOOOOMMMMMmmmmm!!\n\rCaptain, the engines suffered %d units of damage.\r\n", dmg)
	if outputState != "short" {
		repairTime := float32(dmg) / 30
		result += fmt.Sprintf("Captain, repairs will take approximately %.1f stardates.\n\r", repairTime)
	}
	return result
}

// moveShip handles the logic of moving a ship, independent of a connection.
// Called from atomic processor - no locking needed.
func (i *Interpreter) moveShip(ship *Object, targetX int, targetY int, mode string, connInfo *ConnectionInfo) (string, int, error) {
	var msg string
	startX, startY := ship.LocationX, ship.LocationY
	galaxy := ship.Galaxy

	// Validate target coordinates are within galaxy boundaries
	isValid, galaxyMaxX, galaxyMaxY := i.validateGalaxyBoundaries(galaxy, targetX, targetY)
	if !isValid {
		return fmt.Sprintf("Navigation Officer: \"Captain, those coordinates (%d, %d) are outside the galaxy boundaries (1,1 to %d,%d)!\"",
			targetX, targetY, galaxyMaxX, galaxyMaxY), 0, fmt.Errorf("target coordinates outside galaxy boundaries")
	}

	// Check if already at target
	if startX == targetX && startY == targetY {
		return fmt.Sprintf("Already at (%d, %d)", targetX, targetY), 0, nil
	}

	outputState := "short"
	scanType := "short"
	baudRate := DefaultBaudRate
	if connInfo != nil {
		outputState = connInfo.OutputState
		scanType = connInfo.Scan
		baudRate = connInfo.BaudRate
	}

	if ship.WarpEnginesDamage > 0 && ship.WarpEnginesDamage < 30000 {
		if (AbsInt(startX-targetX) > 3) || (AbsInt(startY-targetY) > 3) {
			if outputState == "long" {
				return "Engineering Officer:  The engines won't take it Captain.\r\nI can only give you warp 3.", 0, fmt.Errorf("Engines damaged, warp 3 max")
			} else {
				return "Engines damaged, warp 3 max.", 0, fmt.Errorf("Engines damaged, warp 3 max")
			}
		}
	} else {
		if ship.WarpEnginesDamage >= 30000 {
			return "Warp engines damaged.", 0, fmt.Errorf("Warp engines damaged")
		}
		if (AbsInt(startX-targetX) > 6) || (AbsInt(startY-targetY) > 6) {
			if outputState == "long" {
				return "Engineering Officer:  The engines won't take it Captain.\r\nI can only give you warp 6.", 0, fmt.Errorf("Maximum warp 6")
			} else {
				return "Maximum warp 6.", 0, fmt.Errorf("Maximum warp 6")
			}
		}
	}

	warpDist := max(AbsInt(startX-targetX), AbsInt(startY-targetY))
	i.galaxiesMutex.RLock()
	moveGal := i.galaxies[galaxy]
	i.galaxiesMutex.RUnlock()
	moveRng := newSeededRand()
	if moveGal != nil {
		moveRng = moveGal.rng
	}
	msg += checkEngineOverheating(ship, warpDist, scanType, outputState, moveRng)

	warpFactor := max(AbsInt(startX-targetX), (AbsInt(startY - targetY)))
	cost := CostFactor * warpFactor * warpFactor

	if ship.ShieldsUpDown == true {
		cost = cost * 2
	}
	if ship.TractorOnOff {
		cost = cost * 3
	}
	ship.ShipEnergy = ship.ShipEnergy - cost

	var d float32 = 0
	if ship.ComputerDamage > CriticalDamage {
		d = (float32(moveRng.Float64()) * .5) - 0.25 //Just like decwar
	}

	dist := max(AbsInt(startX-targetX), (AbsInt(startY - targetY)))
	pathCells, finalTargetX, finalTargetY := getPathCells(startX, startY, targetX, targetY, dist, d)

	occupiedCells := make(map[[2]int]bool)
	i.spatialIndexMutex.RLock()
	if galaxyMap, exists := i.objectsByLocation[galaxy]; exists {
		for _, obj := range galaxyMap {
			if obj != ship {
				occupiedCells[[2]int{obj.LocationX, obj.LocationY}] = true
			}
		}
	}
	i.spatialIndexMutex.RUnlock()

	lastSafeCell := [2]int{startX, startY}
	collisionDetected := false
	for _, cell := range pathCells {
		if occupiedCells[cell] {
			collisionDetected = true
			break
		}
		lastSafeCell = cell
	}

	if collisionDetected {
		i.updateObjectLocation(ship, lastSafeCell[0], lastSafeCell[1])
	} else {
		i.updateObjectLocation(ship, finalTargetX, finalTargetY)
	}
	ship.Condition = "Green"

	i.moveTractoredShipIfNeededNoLock(ship, startX, startY, finalTargetX, finalTargetY, pathCells)

	if collisionDetected {
		msg = msg + fmt.Sprintf("Navigation Officer:  \"Collision averted, Captain!\"\n\r")
	}

	dlypse := calculateDlypse(baudRate, startX, startY, finalTargetX, finalTargetY)

	return msg, dlypse, nil
}

// phaserAttack handles the core logic of a phaser attack.
// Called from atomic processor - no locking needed.
func (i *Interpreter) phaserAttack(attacker *Object, target *Object, energy int) (*CombatEvent, error) {
	// Range check
	rangeDist := max(AbsInt(attacker.LocationX-target.LocationX), AbsInt(attacker.LocationY-target.LocationY))
	if rangeDist > MaxRange {
		return nil, fmt.Errorf("Target out of range. Maximum range is %d sectors.", MaxRange)
	}

	// Friendly fire check
	if target.Side == attacker.Side {
		return nil, fmt.Errorf("Weapons Officer:  Attempting to hit friendly object, sir.")
	}

	// Disallow firing at stars with phasers
	if target.Type == "Star" {
		return nil, fmt.Errorf("Phaser control unable to lock on target, sir.")
	}

	// Find attacker and target indexes
	i.spatialIndexMutex.RLock()
	var attackerIdx, targetIdx int = -1, -1
	for idx := range i.objects {
		if i.objects[idx] == attacker {
			attackerIdx = idx
		}
		if i.objects[idx] == target {
			targetIdx = idx
		}
		if attackerIdx != -1 && targetIdx != -1 {
			break
		}
	}
	i.spatialIndexMutex.RUnlock()

	if attackerIdx == -1 || targetIdx == -1 {
		return nil, fmt.Errorf("Could not find attacker or target in objects list.")
	}

	hitType := "Phaser"
	evt, err := i.DoDamage(hitType, targetIdx, attackerIdx, energy*10)
	if err != nil {
		return nil, err
	}

	// Calculate energy consumption for the attacker
	energyCost := energy * 10 // Convert spec units to internal scale (10x)

	// Shield overhead: if attacker ship's shields are up, an additional 200 units
	// (2000 internal) are consumed for high-speed shield control to lower and
	// restore shields during the firing process
	if attacker.Type == "Ship" && attacker.ShieldsUpDown {
		energyCost += 2000 // 200 spec units * 10 internal scale
	}

	attacker.ShipEnergy -= energyCost
	attacker.Condition = "Red"

	// Self-damage risk for ship phaser banks:
	// 5% chance at 200 energy, scaling linearly to ~65% at 500 energy.
	// Below 200 energy the probability decreases linearly (clamped to 0%).
	if attacker.Type == "Ship" {
		selfDamageProb := 0.05 + float64(energy-200)*0.002
		if selfDamageProb < 0 {
			selfDamageProb = 0
		}
		i.galaxiesMutex.RLock()
		phaserGal := i.galaxies[attacker.Galaxy]
		i.galaxiesMutex.RUnlock()
		phaserRng := newSeededRand()
		if phaserGal != nil {
			phaserRng = phaserGal.rng
		}
		if phaserRng.Float64() < selfDamageProb {
			// Severity of self-damage is proportional to the blast size
			selfDamageAmt := energy / 2
			if selfDamageAmt < 1 {
				selfDamageAmt = 1
			}
			attacker.PhasersDamage += selfDamageAmt
		}
	}

	return evt, nil
}

// torpedoAttack handles the logic of firing torpedoes.
// Called from atomic processor - no locking needed.
func (i *Interpreter) torpedoAttack(attacker *Object, vpos, hpos, numTorps int, connInfo *ConnectionInfo) (string, error) {
	if attacker.TorpedoTubes < numTorps {
		return fmt.Sprintf("Insufficient torpedoes for burst!\n\r%d torpedos left.\n\r", attacker.TorpedoTubes), nil
	}

	var attackerIdx = -1
	i.spatialIndexMutex.RLock()
	for idx := range i.objects {
		if i.objects[idx] == attacker {
			attackerIdx = idx
			break
		}
	}
	i.spatialIndexMutex.RUnlock()
	if attackerIdx == -1 {
		return "", fmt.Errorf("could not find attacker in objects list")
	}

	result := ""
	i.galaxiesMutex.RLock()
	torpGal := i.galaxies[attacker.Galaxy]
	i.galaxiesMutex.RUnlock()
	torpRng := newSeededRand()
	if torpGal != nil {
		torpRng = torpGal.rng
	}
	for torpCount := 0; torpCount < numTorps; torpCount++ {
		if attacker.TorpedoTubes < 1 {
			result += fmt.Sprintf("Insufficient torpedoes for burst!\n\r%d torpedos left.\n\r", attacker.TorpedoTubes)
			break
		}

		attacker.TorpedoTubes--

		deflection := i.calculateTorpedoDeflection(attacker, torpRng)
		actualTargetIdx, objectfound, endX, endY := i.torpedoPathLocked(attacker.LocationX, attacker.LocationY, vpos, hpos, attacker.Galaxy, deflection)

		if !objectfound {
			if connInfo != nil {
				// format miss message
				outputst := connInfo.OutputState
				formt := connInfo.OCdef
				if outputst == "long" {
					if formt == "relative" {
						result = result + fmt.Sprintf("Weapons Officer:  Sir, torpedo %d lost %+d,%+d\n\r", torpCount+1, endX-attacker.LocationX, endY-attacker.LocationY)
					} else if formt == "absolute" {
						result = result + fmt.Sprintf("Weapons Officer:  Sir, torpedo %d lost @%d-%d\n\r", torpCount+1, endX, endY)
					} else {
						result = result + fmt.Sprintf("Weapons Officer:  Sir, torpedo %d lost @%d-%d %+d,%+d\n\r", torpCount+1, endX, endY, endX-attacker.LocationX, endY-attacker.LocationY)
					}
				} else {
					result = result + fmt.Sprintf("T%d miss\n\r", torpCount+1)
				}
			} else {
				result += fmt.Sprintf("T%d miss\n\r", torpCount+1)
			}
			continue
		}

		i.spatialIndexMutex.RLock()
		target := i.objects[actualTargetIdx]
		if target != nil && target == attacker {
			result += "ERROR detected by computer!!\r\nYou have attempted to use your present location.\n\r"
			i.spatialIndexMutex.RUnlock()
			continue
		}
		if target.Side == attacker.Side {
			result += fmt.Sprintf("Weapons Officer:  Attempting to hit friendly object @%d-%d\n\r", target.LocationX, target.LocationY)
			i.spatialIndexMutex.RUnlock()
			continue
		}
		i.spatialIndexMutex.RUnlock()

		evt, err := i.DoDamage("Torpedo", actualTargetIdx, attackerIdx, 0)
		if err != nil {
			result += fmt.Sprintf("Error firing torpedo: %s\n\r", err.Error())
			continue
		}

		if connInfo != nil {
			// Find the net.Conn associated with this ConnectionInfo
			var playerConn net.Conn
			i.connections.Range(func(key, value interface{}) bool {
				conn := key.(net.Conn)
				ci := value.(ConnectionInfo)
				if &ci == connInfo {
					playerConn = conn
					return false
				}
				return true
			})
			if playerConn != nil {
				i.BroadcastCombatEvent(evt, playerConn)
			}
		}

		if evt.Message == "destroyed" {
			targetConn := i.getShipConnection(*target)
			if targetConn != nil {
				if writerRaw, ok := i.writers.Load(targetConn); ok {
					writer := writerRaw.(*bufio.Writer)
					var msg string
					if target.Type == "Star" {
						msg = fmt.Sprintf("Star @%d-%d novas\r\n", target.LocationX, target.LocationY)
					} else {
						msg = fmt.Sprintf("%s has been destroyed!\r\n", target.Name)
					}
					i.writeBaudf(targetConn, writer, "%s", msg)
				}

				if targetConnInfo, ok := i.connections.Load(targetConn); ok {
					ci := targetConnInfo.(ConnectionInfo)
					// Set destruction cooldown when ship is destroyed and player returns to pregame
					i.setDestructionCooldownForConn(ci, target.Galaxy)
					// Reset enteredTime when ship is destroyed and player returns to pregame
					if ci.Ship != nil {
						ci.Ship.EnteredTime = nil
					}
					ci.Section = "pregame"
					ci.Shipname = ""
					ci.Ship = nil
					ci.Galaxy = 0
					ci.BaudRate = 0
					i.connections.Store(targetConn, ci)
				}
			}
			i.removeObjectByIndex(actualTargetIdx)
			// Adjust attackerIdx since removing an object shifts indices down
			if actualTargetIdx < attackerIdx {
				attackerIdx--
			}
		}
	}

	attacker.Condition = "Red"
	return result, nil
}

// registerCommands adds commands to their respective sections
func (i *Interpreter) registerCommands() {
	// galaxyStats is used by summary handlers in both pregame and gowars sections
	type galaxyStats struct {
		FederationBases   int
		EmpireBases       int
		BlackHoles        int
		NeutralPlanets    int
		FederationPlanets int
		EmpirePlanets     int
		Stars             int
		Ships             int
	}

	// Pregame commands
	i.pregameCommands["quit"] = Command{
		Handler: func(args []string, conn net.Conn) string {
			// Print Goodbye and close the connection
			fmt.Fprintf(conn, "Goodbye\r\n")
			conn.Close()
			return ""
		},
		Help: "QUIT the game\r\n" +
			"Syntax: Quit\r\n" +
			"\r\n" +
			"Quit the game before normal end of execution and return to the\r\n" +
			"monitor. Your ship is released for use by another player, you're\r\n" +
			"chalked up as just one more casualty, and you can't CONTINUE the game.\r\n" +
			"If you want to rejoin the game, you'll have to wait 2 minutes, and\r\n" +
			"then either START or RUN the game. If you want to exit the game\r\n" +
			"temporarily (to answer SENDS, etc.), type ^C (CTL-C), and you'll\r\n" +
			"usually be able to CONTINUE. NOTE: If you're under red alert, you\r\n" +
			"won't be able to ^C out of the game; you'll have to use the QUIT\r\n" +
			"command."}

	i.pregameCommands["time"] = Command{
		// From decwar:
		// Game's elapsed time:  01:50:57
		// Ship's elapsed time:  01:50:53
		// Run time in game:     00:00:00
		// Job's total run time: 00:00:00
		// Current time of day:  15:03:00
		Handler: func(args []string, conn net.Conn) string {
			now := time.Now()
			programDuration := now.Sub(i.programStart)

			var galaxyElapsedTime, enteredTimeStr, connTimeStr string

			// Get connection info
			infoRaw, ok := i.connections.Load(conn)
			if ok {
				info := infoRaw.(ConnectionInfo)
				// Get galaxy start time
				i.trackerMutex.Lock()
				if tracker, exists := i.galaxyTracker[info.Galaxy]; exists {
					elapsed := now.Sub(tracker.GalaxyStart)
					h := int(elapsed.Hours())
					m := int(elapsed.Minutes()) % 60
					s := int(elapsed.Seconds()) % 60
					galaxyElapsedTime = fmt.Sprintf("%02d:%02d:%02d", h, m, s)
				} else {
					galaxyElapsedTime = "N/A"
				}
				i.trackerMutex.Unlock()

				// Get enteredTime from ship
				if info.Ship != nil && info.Ship.EnteredTime != nil {
					shipElapsed := time.Since(*info.Ship.EnteredTime)
					h := int(shipElapsed.Hours())
					m := int(shipElapsed.Minutes()) % 60
					s := int(shipElapsed.Seconds()) % 60
					enteredTimeStr = fmt.Sprintf("%02d:%02d:%02d", h, m, s)
				} else {
					enteredTimeStr = "N/A"
				}

				// Get connection time
				connElapsed := time.Since(info.ConnTime)
				h := int(connElapsed.Hours())
				m := int(connElapsed.Minutes()) % 60
				s := int(connElapsed.Seconds()) % 60
				connTimeStr = fmt.Sprintf("%02d:%02d:%02d", h, m, s)
			} else {
				galaxyElapsedTime = "N/A"
				enteredTimeStr = "N/A"
				connTimeStr = "N/A"
			}

			// Check if the connection is in pregame
			if info, ok := i.connections.Load(conn); ok {
				if info.(ConnectionInfo).Section == "pregame" {
					galaxyElapsedTime = "N/A"
				}
			}
			// Format Job's total run time as HH:MM:SS
			h := int(programDuration.Hours())
			m := int(programDuration.Minutes()) % 60
			s := int(programDuration.Seconds()) % 60
			jobRunTime := fmt.Sprintf("%02d:%02d:%02d", h, m, s)
			return fmt.Sprintf(
				"Galaxy elapsed time:\t%s\r\nShip's elapsed time:\t%s\r\nRun time in game:\t%s\r\nJob's total run time:\t%s\r\nCurrent time of day:\t%s",
				galaxyElapsedTime,
				connTimeStr,
				enteredTimeStr,
				jobRunTime,
				now.Format("15:04:05"))
		},
		Help: "Display current date/time and program uptime",
	}
	i.pregameCommands["news"] = Command{
		Handler: func(args []string, conn net.Conn) string {
			data, err := os.ReadFile("gowars.nws")
			if err != nil {
				return fmt.Sprintf("Error reading gowars.nws: %v", err)
			}
			lines := strings.Split(string(data), "\n")
			for i, line := range lines {
				lines[i] = strings.TrimRight(line, "\r")
			}
			return strings.Join(lines, "\r\n")
		},
		Help: "Display the NEWS file\r\n" +
			"Syntax: NEws\r\n" +
			"\r\n" +
			"Display gowars.nws, which contains information on any new\r\n" +
			"features, enhancements, bug fixes, etc for each version of gowars.",
	}
	i.pregameCommands["gripe"] = Command{
		Handler: func(args []string, conn net.Conn) string {
			if len(args) == 0 {
				data, err := os.ReadFile("gripe.txt")
				if err != nil {
					return fmt.Sprintf("Error reading gripe.txt: %v", err)
				}
				lines := strings.Split(string(data), "\n")
				for idx, line := range lines {
					lines[idx] = strings.TrimRight(line, "\r")
				}
				return strings.Join(lines, "\r\n")
			}

			// Sanitize gripe text
			gripeText := sanitizeGripeText(strings.Join(args, " "))
			if gripeText == "" {
				return "Error: gripe text cannot be empty or contain only control characters"
			}

			// Get connection info for IP logging
			var sourceIP string
			if info, ok := i.connections.Load(conn); ok {
				connInfo := info.(ConnectionInfo)
				sourceIP = connInfo.IP
			} else {
				// Fallback to getting IP from connection
				if addr := conn.RemoteAddr(); addr != nil {
					sourceIP, _, _ = net.SplitHostPort(addr.String())
				}
			}

			// Rotate gripe file if needed
			if err := rotateGripeFile("gripe.txt"); err != nil {
				log.Printf("Error rotating gripe file: %v", err)
			}

			file, err := os.OpenFile("gripe.txt", os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0644)
			if err != nil {
				return fmt.Sprintf("Error writing to gripe.txt: %v", err)
			}
			defer file.Close()

			// Write gripe with timestamp and source IP
			timestamp := time.Now().Format(time.RFC3339)
			if _, err := fmt.Fprintf(file, "[%s] [%s] %s\n", timestamp, sourceIP, gripeText); err != nil {
				return fmt.Sprintf("Error writing to gripe.txt: %v", err)
			}

			return fmt.Sprintf("Gripe recorded: %s", gripeText)
		},
		Help: "With text: append to gripe.txt; without text: display gripe.txt contents",
	}
	i.pregameCommands["users"] = Command{
		Handler: func(args []string, conn net.Conn) string {
			var lines []string
			// Check output state
			outputShort := false
			if info, ok := i.connections.Load(conn); ok {
				connInfo := info.(ConnectionInfo)
				if connInfo.OutputState == "short" {
					outputShort = true
				}
			}
			if outputShort {
				lines = append(lines, "Galaxy   Ship           Captain       Speed")
				lines = append(lines, strings.Repeat("-", 43))
			} else {
				lines = append(lines, "Galaxy   Ship           Captain       Speed	Connection Info")
				lines = append(lines, strings.Repeat("-", 63))
			}
			i.connections.Range(func(_, value interface{}) bool {
				info := value.(ConnectionInfo)
				galaxyStr := "None    "
				if info.Section == "gowars" {
					galaxyStr = fmt.Sprintf("%-8d", info.Galaxy)
				}
				shipnameStr := "None           "
				if info.Section == "gowars" && info.Shipname != "" {
					if info.AdminMode == true {
						shipnameStr = fmt.Sprintf("*")
					} else {
						shipnameStr = fmt.Sprintf(" ")
					}
					shipnameStr = shipnameStr + fmt.Sprintf("%-16s", info.Shipname)
				}
				usernameStr := "None           "
				speedStr := fmt.Sprintf("%d", info.BaudRate)
				if info.Name != "" {
					usernameStr = fmt.Sprintf("%-16s", info.Name)
				}
				if outputShort {
					lines = append(lines, fmt.Sprintf("%s %s%s%s", galaxyStr, shipnameStr, usernameStr, speedStr))
				} else {
					connInfoStr := fmt.Sprintf("%s:%s", info.IP, info.Port)
					lines = append(lines, fmt.Sprintf("%s %s%s%s\t%s", galaxyStr, shipnameStr, usernameStr, speedStr, connInfoStr))
				}
				return true
			})
			return strings.Join(lines, "\r\n")
		},
		Help: "List USERS\r\n" +
			"Syntax: Users\r\n" +
			"\r\n" +
			"List all ships currently in the game. Include ship name, captain (may\r\n" +
			"be changed by SET NAME), TTY speed, PPN, TTY number, and job number.\r\n" +
			"If the output format is set to medium or short, omit the TTY and job\r\n" +
			"numbers. If the output format is set to short, omit the TTY speed and\r\n" +
			"PPN (include only the ship name and captain).",
	}
	i.pregameCommands["activate"] = Command{
		Handler: func(args []string, conn net.Conn) string {
			var galaxy uint16 = 0
			var preferredSide string
			params := getDefaultGalaxyParams()
			// Parse parameters: Side Galaxy DecwarMode MaxSizeX MaxSizeY MaxRomulans MaxBlackHoles MaxNeutralPlanets MaxFederationPlanets MaxEmpirePlanets MaxStars MaxBasesPerSide
			if len(args) > 12 {
				return "Error: activate takes at most 12 parameters: Side Galaxy DecwarMode MaxSizeX MaxSizeY MaxRomulans MaxBlackHoles MaxNeutralPlanets MaxFederationPlanets MaxEmpirePlanets MaxStars MaxBasesPerSide"
			}

			// Parse Side parameter (optional)
			argOffset := 0
			if len(args) >= 1 {
				// Check if first argument looks like a side specification
				firstArg := strings.ToLower(args[0])

				// Check for valid side abbreviations (not numeric)
				if firstArg == "f" || strings.HasPrefix("federation", firstArg) {
					preferredSide = "federation"
					argOffset = 1
				} else if firstArg == "e" || strings.HasPrefix("empire", firstArg) {
					preferredSide = "empire"
					argOffset = 1
				}
			}

			// Parse Galaxy parameter
			if len(args) >= 1+argOffset {
				galaxyNum, err := strconv.ParseUint(args[argOffset], 10, 16)
				if err != nil || galaxyNum > 65535 {
					return "Error: galaxy must be a number between 0 and 65535"
				}
				galaxy = uint16(galaxyNum)
			}

			// --- Destruction cooldown enforcement ---
			if info, ok := i.connections.Load(conn); ok {
				connInfo := info.(ConnectionInfo)
				key := connInfo.IP + ":" + connInfo.Port

				// Check if cooldown exists for this (IP:Port, Galaxy)
				i.destroyedCooldownsMutex.Lock()
				var cooldownActive bool
				var cooldownExpiry time.Time
				if galaxyMap, ok := i.destroyedCooldowns[key]; ok {
					if destroyedAt, ok := galaxyMap[galaxy]; ok {
						// Always enforce cooldown for full duration after destruction
						if time.Since(destroyedAt) < 2*time.Minute {
							cooldownActive = true
							cooldownExpiry = destroyedAt.Add(2 * time.Minute)
						} else {
							// Cooldown expired, clear it
							delete(galaxyMap, galaxy)
						}
					}
				}
				i.destroyedCooldownsMutex.Unlock()
				if cooldownActive {
					remaining := time.Until(cooldownExpiry).Round(time.Second)
					if remaining < time.Second {
						remaining = 2 * time.Minute
					}
					return fmt.Sprintf("You must wait %s to re-enter the galaxy.", remaining)
				}
			}

			// Parse DecwarMode parameter
			if len(args) >= 2+argOffset {
				decwarMode, err := strconv.ParseBool(args[1+argOffset])
				if err != nil {
					return "Error: DecwarMode must be true or false"
				}
				params.DecwarMode = decwarMode
			}

			// Parse MaxSizeX parameter
			if len(args) >= 3+argOffset {
				maxSizeX, err := strconv.Atoi(args[2+argOffset])
				if err != nil {
					return "Error: MaxSizeX must be a number"
				}
				params.MaxSizeX = maxSizeX
			}

			// Parse MaxSizeY parameter
			if len(args) >= 4+argOffset {
				maxSizeY, err := strconv.Atoi(args[3+argOffset])
				if err != nil {
					return "Error: MaxSizeY must be a number"
				}
				params.MaxSizeY = maxSizeY
			}

			// Parse MaxRomulans parameter
			if len(args) >= 5+argOffset {
				maxRomulans, err := strconv.Atoi(args[4+argOffset])
				if err != nil {
					return "Error: MaxRomulans must be a number"
				}
				params.MaxRomulans = maxRomulans
			}

			// Parse MaxBlackHoles parameter
			if len(args) >= 6+argOffset {
				maxBlackHoles, err := strconv.Atoi(args[5+argOffset])
				if err != nil {
					return "Error: MaxBlackHoles must be a number"
				}
				params.MaxBlackHoles = maxBlackHoles
			}

			// Parse MaxNeutralPlanets parameter
			if len(args) >= 7+argOffset {
				maxNeutralPlanets, err := strconv.Atoi(args[6+argOffset])
				if err != nil {
					return "Error: MaxNeutralPlanets must be a number"
				}
				params.MaxNeutralPlanets = maxNeutralPlanets
			}

			// Parse MaxFederationPlanets parameter
			if len(args) >= 8+argOffset {
				maxFederationPlanets, err := strconv.Atoi(args[7+argOffset])
				if err != nil {
					return "Error: MaxFederationPlanets must be a number"
				}
				params.MaxFederationPlanets = maxFederationPlanets
			}

			// Parse MaxEmpirePlanets parameter
			if len(args) >= 9+argOffset {
				maxEmpirePlanets, err := strconv.Atoi(args[8+argOffset])
				if err != nil {
					return "Error: MaxEmpirePlanets must be a number"
				}
				params.MaxEmpirePlanets = maxEmpirePlanets
			}

			// Parse MaxStars parameter
			if len(args) >= 10+argOffset {
				maxStars, err := strconv.Atoi(args[9+argOffset])
				if err != nil {
					return "Error: MaxStars must be a number"
				}
				params.MaxStars = maxStars
			}

			// Parse MaxBasesPerSide parameter
			if len(args) >= 11+argOffset {
				maxBasesPerSide, err := strconv.Atoi(args[10+argOffset])
				if err != nil {
					return "Error: MaxBasesPerSide must be a number"
				}
				params.MaxBasesPerSide = maxBasesPerSide
			}

			// Validate parameters
			if err := validateGalaxyParams(galaxy, params); err != nil {
				return fmt.Sprintf("Error: %v", err)
			}

			if info, ok := i.connections.Load(conn); ok {
				connInfo := info.(ConnectionInfo)

				// Determine side assignment
				var side string
				if preferredSide != "" {
					// Side was specified in command, use it
					side = preferredSide
				} else if connInfo.PreferredSide != "" {
					// Player has a preferred side, try to use it
					side = connInfo.PreferredSide
				} else {
					// First time player, assign side by alternating
					i.lastSideMutex.Lock()
					side = "federation"
					if i.lastSide == "federation" {
						side = "empire"
					}
					i.lastSide = side
					i.lastSideMutex.Unlock()

					// Record this as their preferred side
					connInfo.PreferredSide = side
				}

				// Check if there are any active connections in this galaxy (Section != "pregame"); if not, initialize it
				hasPlayers := false
				i.connections.Range(func(_, value interface{}) bool {
					ci := value.(ConnectionInfo)
					if ci.Galaxy == galaxy && ci.Section != "pregame" {
						hasPlayers = true
						return false // found a player in galaxy and not in pregame, stop iteration
					}
					return true
				})
				galaxyCreated := false
				if !hasPlayers {
					i.resetAndReinitializeGalaxy(galaxy, params)
					galaxyCreated = true
				}

				// Look for available ships of the player's preferred side
				var availableShips []string
				fedNames := []string{"Excalibur", "Farragut", "Intrepid", "Lexington", "Nimitz", "Savannah", "Trenton", "Vulcan", "Yorktown"}
				empNames := []string{"Buzzard", "Cobra", "Demon", "Goblin", "Hawk", "Jackal", "Manta", "Panther", "Wolf"}

				var sideNames []string
				if side == "federation" {
					sideNames = fedNames
				} else {
					sideNames = empNames
				}

				// Check which ships are already in use in this galaxy
				usedShips := make(map[string]bool)
				i.connections.Range(func(_, value interface{}) bool {
					ci := value.(ConnectionInfo)
					if ci.Shipname != "" && ci.Galaxy == galaxy {
						usedShips[ci.Shipname] = true
					}
					return true
				})

				// Also check existing ship objects in case cleanup hasn't run yet
				ships := i.getObjectsByType(galaxy, "Ship")
				if ships != nil {
					for _, obj := range ships {
						// Skip Romulan ships as they're NPCs
						if !strings.HasPrefix(obj.Name, "Romulan") {
							usedShips[obj.Name] = true
						}
					}
				}

				// Find available ships for this side
				for _, name := range sideNames {
					if !usedShips[name] {
						availableShips = append(availableShips, name)
					}
				}

				// If no ships available for preferred side, return error
				if len(availableShips) == 0 {
					return "No ships available for your side"
				}

				// Assign random available ship
				i.galaxiesMutex.RLock()
				actGal := i.galaxies[galaxy]
				i.galaxiesMutex.RUnlock()
				actRng := newSeededRand()
				if actGal != nil {
					actRng = actGal.rng
				}
				shipname := availableShips[actRng.Intn(len(availableShips))]

				connInfo.Section = "gowars"
				connInfo.Galaxy = galaxy
				connInfo.Shipname = shipname
				// Set prompt to "normal" when ship enters the game
				connInfo.Prompt = "normal"
				// Set default baud rate based on galaxy's DecwarMode
				// For existing galaxies, use the stored galaxy params instead of the user-provided params
				effectiveDecwarMode := params.DecwarMode
				if !galaxyCreated {
					i.galaxyParamsMutex.RLock()
					if gp, gpOk := i.galaxyParams[galaxy]; gpOk {
						effectiveDecwarMode = gp.DecwarMode
					}
					i.galaxyParamsMutex.RUnlock()
				}
				if effectiveDecwarMode {
					connInfo.BaudRate = DefaultBaudRate
				} else {
					connInfo.BaudRate = 0
				}

				// Create a Ship object with the assigned side and shipname
				occupied := make(map[string]struct{})
				i.spatialIndexMutex.RLock()
				if galaxyMap, exists := i.objectsByLocation[galaxy]; exists {
					for locKey := range galaxyMap {
						occupied[locKey] = struct{}{}
					}
				}
				i.spatialIndexMutex.RUnlock()

				// Determine actual galaxy size - for new galaxies use custom params, for existing galaxies get from tracker
				actualMaxX := params.MaxSizeX
				actualMaxY := params.MaxSizeY

				if !galaxyCreated {
					i.trackerMutex.Lock()
					if tracker, exists := i.galaxyTracker[galaxy]; exists {
						if tracker.MaxSizeX > 0 {
							actualMaxX = tracker.MaxSizeX
						} else {
							actualMaxX = MaxSizeX
						}
						if tracker.MaxSizeY > 0 {
							actualMaxY = tracker.MaxSizeY
						} else {
							actualMaxY = MaxSizeY
						}
					} else {
						actualMaxX = MaxSizeX
						actualMaxY = MaxSizeY
					}
					i.trackerMutex.Unlock()
				}

				var x, y int
				for {
					x = actRng.Intn(actualMaxX) + 1
					y = actRng.Intn(actualMaxY) + 1
					key := fmt.Sprintf("%d,%d", x, y)
					if _, exists := occupied[key]; !exists {
						break
					}
				}
				enteredTime := time.Now()
				obj := Object{
					Galaxy:             galaxy,
					Type:               "Ship",
					LocationX:          x,
					LocationY:          y,
					Side:               side,
					Name:               shipname,
					Shields:            InitialShieldValue, // Default shields for new ships
					Condition:          "Green",
					TorpedoTubes:       10,
					TorpedoTubeDamage:  0,
					PhasersDamage:      0,
					ComputerDamage:     0,
					LifeSupportDamage:  0,
					LifeSupportReserve: 5,
					RadioOnOff:         true,
					RadioDamage:        0,
					TractorOnOff:       false,
					TractorShip:        "",
					TractorDamage:      0,
					ShieldsUpDown:      true,
					ShipEnergy:         InitialShipEnergy,
					SeenByFed:          false,
					SeenByEmp:          false,
					TotalShipDamage:    0,
					WarpEnginesDamage:  0,
					Builds:             0,
					EnteredTime:        &enteredTime, // Set entered time when ship enters the game
				}
				i.addObjectToObjects(obj)
				// Set the Ship pointer to the newly created ship by finding it properly
				ship := i.getShipByName(galaxy, shipname)
				if ship != nil {
					connInfo.Ship = ship
				}
				i.connections.Store(conn, connInfo)

				// Update galaxy tracker
				i.trackerMutex.Lock()
				if tracker, exists := i.galaxyTracker[galaxy]; exists {
					tracker.LastActive = time.Now()
					i.galaxyTracker[galaxy] = tracker
				} else {
					now := time.Now()
					i.galaxyTracker[galaxy] = GalaxyTracker{GalaxyStart: now, LastActive: now, MaxSizeX: params.MaxSizeX, MaxSizeY: params.MaxSizeY, MaxRomulans: params.MaxRomulans, DecwarMode: params.DecwarMode}
				}
				i.trackerMutex.Unlock()

				i.connections.Store(conn, connInfo)

				var msg string
				if galaxyCreated {
					msg = fmt.Sprintf("Galaxy %d created with custom parameters (Size: %dx%d).\n\r", galaxy, params.MaxSizeX, params.MaxSizeY)
				} else {
					msg = fmt.Sprintf("Galaxy %d already exists - using existing galaxy.\n\r", galaxy)
				}

				if params.MaxRomulans > 0 {
					msg = msg + "There are Romulans in this game.\n\r"
				}
				if side == "federation" {
					msg = msg + "You will join the forces of the Federation.\n\r"
				} else {
					msg = msg + "You will join the forces of the Klingon Empire.\n\r"
				}

				if params.DecwarMode == true {
					msg = msg + fmt.Sprintf("Entering Decwars as %s ship '%s' in galaxy %d", side, shipname, galaxy)
				} else {
					msg = msg + fmt.Sprintf("Entering GOWARS as %s ship '%s' in galaxy %d", side, shipname, galaxy)
				}
				return msg
			}
			return "Error switching to GOWARS"
		},
		Help: "Enter/Create a Galaxy optional parameters:\r\n" +
			"activate [Side] [Galaxy] [DecwarMode] [MaxSizeX] [MaxSizeY] [MaxRomulans] [MaxBlackHoles] [MaxNeutralPlanets] [MaxFederationPlanets] [MaxEmpirePlanets] [MaxStars] [MaxBasesPerSide]\r\n" +
			"Side: fed/federation or emp/empire (optional, defaults to alternating assignment)\r\n" +
			"Galaxy: 0-" + strconv.Itoa(MaxGalaxies-1) + " (default: 0)\r\n" +
			"DecwarMode: true/false (default: " + strconv.FormatBool(DecwarMode) + ")\r\n" +
			"MaxSizeX, MaxSizeY: 21-99 (default: " + strconv.Itoa(MaxSizeX) + ", " + strconv.Itoa(MaxSizeY) + ")\r\n" +
			"All other params: 0-9999, sum must be < 10000\r\n" +
			"Ex: act fed 3 false 50 50 5 10 15 8 8 100 5",
	}
	i.pregameCommands["summary"] = Command{
		Handler: func(args []string, conn net.Conn) string {
			var arg string
			if len(args) == 0 {
				arg = "all"
			} else {
				validParams := map[string]bool{"all": true, "list": true}
				if resolved, ok := i.resolveParameter(strings.ToLower(args[0]), validParams); ok {
					arg = resolved
				} else {
					arg = strings.ToLower(args[0])
				}
			}

			totalUsers := 0
			i.connections.Range(func(key, value interface{}) bool {
				totalUsers++
				return true
			})

			var lines []string

			if arg == "list" {
				// Collect all active galaxy IDs
				galaxySet := make(map[uint16]struct{})
				i.spatialIndexMutex.RLock()
				for _, obj := range i.objects {
					galaxySet[obj.Galaxy] = struct{}{}
				}
				i.spatialIndexMutex.RUnlock()

				if len(galaxySet) == 0 {
					return "\r\nNo active galaxies.\r\n"
				}

				// Sort galaxy IDs
				sortedGalaxies := make([]uint16, 0, len(galaxySet))
				for gid := range galaxySet {
					sortedGalaxies = append(sortedGalaxies, gid)
				}
				sort.Slice(sortedGalaxies, func(a, b int) bool {
					return sortedGalaxies[a] < sortedGalaxies[b]
				})

				// Header
				lines = append(lines, "")
				lines = append(lines, fmt.Sprintf("%-7s %7s %7s %7s %7s %7s %7s %7s %7s %10s %6s %6s",
					"Galaxy", "FedBas", "EmpBas", "BHoles", "NeuPln", "FedPln", "EmpPln", "Stars", "Ships", "DecwarMode", "MaxX", "MaxY"))
				lines = append(lines, fmt.Sprintf("%-7s %7s %7s %7s %7s %7s %7s %7s %7s %10s %6s %6s",
					"------", "------", "------", "------", "------", "------", "------", "------", "------", "----------", "----", "----"))

				for _, gid := range sortedGalaxies {
					stats := &galaxyStats{}

					ships := i.getObjectsByType(gid, "Ship")
					stats.Ships = len(ships)
					stars := i.getObjectsByType(gid, "Star")
					stats.Stars = len(stars)
					blackholes := i.getObjectsByType(gid, "Black Hole")
					stats.BlackHoles = len(blackholes)

					bases := i.getObjectsByType(gid, "Base")
					for _, base := range bases {
						if base.Side == "federation" {
							stats.FederationBases++
						} else if base.Side == "empire" {
							stats.EmpireBases++
						}
					}

					planets := i.getObjectsByType(gid, "Planet")
					for _, planet := range planets {
						switch planet.Side {
						case "neutral":
							stats.NeutralPlanets++
						case "federation":
							stats.FederationPlanets++
						case "empire":
							stats.EmpirePlanets++
						}
					}

					// Get galaxy params for decwarmode and sizes
					decwarStr := "false"
					maxX := MaxSizeX
					maxY := MaxSizeY
					i.galaxyParamsMutex.RLock()
					if gp, gpOk := i.galaxyParams[gid]; gpOk {
						if gp.DecwarMode {
							decwarStr = "true"
						}
						maxX = gp.MaxSizeX
						maxY = gp.MaxSizeY
					}
					i.galaxyParamsMutex.RUnlock()

					lines = append(lines, fmt.Sprintf("%-7d %7d %7d %7d %7d %7d %7d %7d %7d %10s %6d %6d",
						gid, stats.FederationBases, stats.EmpireBases, stats.BlackHoles,
						stats.NeutralPlanets, stats.FederationPlanets, stats.EmpirePlanets,
						stats.Stars, stats.Ships, decwarStr, maxX, maxY))
				}
			} else if arg == "all" {
				grandTotals := &galaxyStats{}
				galaxySet := make(map[uint16]struct{})

				i.spatialIndexMutex.RLock()
				for _, obj := range i.objects {
					galaxySet[obj.Galaxy] = struct{}{}
					switch obj.Type {
					case "Ship":
						grandTotals.Ships++
					case "Star":
						grandTotals.Stars++
					case "Black Hole":
						grandTotals.BlackHoles++
					}
				}
				i.spatialIndexMutex.RUnlock()

				for galaxyID := range galaxySet {
					bases := i.getObjectsByType(galaxyID, "Base")
					for _, base := range bases {
						if base.Side == "federation" {
							grandTotals.FederationBases++
						} else if base.Side == "empire" {
							grandTotals.EmpireBases++
						}
					}
					planets := i.getObjectsByType(galaxyID, "Planet")
					for _, planet := range planets {
						switch planet.Side {
						case "neutral":
							grandTotals.NeutralPlanets++
						case "federation":
							grandTotals.FederationPlanets++
						case "empire":
							grandTotals.EmpirePlanets++
						}
					}
				}

				lines = append(lines, fmt.Sprintf("\r\nTotal players online: %d", totalUsers))
				lines = append(lines, fmt.Sprintf("Active galaxies: %d\r\n", len(galaxySet)))

				if len(galaxySet) > 0 {
					lines = append(lines, "Grand Totals Across All Galaxies:")
					lines = append(lines, fmt.Sprintf("  Federation Bases: %d", grandTotals.FederationBases))
					lines = append(lines, fmt.Sprintf("  Empire Bases: %d", grandTotals.EmpireBases))
					lines = append(lines, fmt.Sprintf("  Black Holes: %d", grandTotals.BlackHoles))
					lines = append(lines, fmt.Sprintf("  Neutral Planets: %d", grandTotals.NeutralPlanets))
					lines = append(lines, fmt.Sprintf("  Federation Planets: %d", grandTotals.FederationPlanets))
					lines = append(lines, fmt.Sprintf("  Empire Planets: %d", grandTotals.EmpirePlanets))
					lines = append(lines, fmt.Sprintf("  Stars: %d", grandTotals.Stars))
					lines = append(lines, fmt.Sprintf("  Ships: %d", grandTotals.Ships))
				}
			} else {
				galaxyID, err := strconv.Atoi(arg)
				if err != nil {
					return "Invalid argument. Please specify 'all' or a galaxy number.\r\n"
				}

				totals := &galaxyStats{}

				i.galaxiesMutex.RLock()
				_, galaxyExists := i.galaxies[uint16(galaxyID)]
				i.galaxiesMutex.RUnlock()

				if !galaxyExists {
					return fmt.Sprintf("Galaxy %d not found.\r\n", galaxyID)
				}

				ships := i.getObjectsByType(uint16(galaxyID), "Ship")
				totals.Ships = len(ships)
				stars := i.getObjectsByType(uint16(galaxyID), "Star")
				totals.Stars = len(stars)
				blackholes := i.getObjectsByType(uint16(galaxyID), "Black Hole")
				totals.BlackHoles = len(blackholes)

				bases := i.getObjectsByType(uint16(galaxyID), "Base")
				for _, base := range bases {
					if base.Side == "federation" {
						totals.FederationBases++
					} else if base.Side == "empire" {
						totals.EmpireBases++
					}
				}

				planets := i.getObjectsByType(uint16(galaxyID), "Planet")
				for _, planet := range planets {
					switch planet.Side {
					case "neutral":
						totals.NeutralPlanets++
					case "federation":
						totals.FederationPlanets++
					case "empire":
						totals.EmpirePlanets++
					}
				}

				lines = append(lines, fmt.Sprintf("\r\nSummary for Galaxy %d:", galaxyID))
				lines = append(lines, fmt.Sprintf("  Federation Bases: %d", totals.FederationBases))
				lines = append(lines, fmt.Sprintf("  Empire Bases: %d", totals.EmpireBases))
				lines = append(lines, fmt.Sprintf("  Black Holes: %d", totals.BlackHoles))
				lines = append(lines, fmt.Sprintf("  Neutral Planets: %d", totals.NeutralPlanets))
				lines = append(lines, fmt.Sprintf("  Federation Planets: %d", totals.FederationPlanets))
				lines = append(lines, fmt.Sprintf("  Empire Planets: %d", totals.EmpirePlanets))
				lines = append(lines, fmt.Sprintf("  Stars: %d", totals.Stars))
				lines = append(lines, fmt.Sprintf("  Ships: %d", totals.Ships))
			}

			return strings.Join(lines, "\r\n")
		},
		Help: "Give SUMMARY on number of ships, bases, and planets for one or all galaxies\r\nsummary [all|list|<galaxy_id>]\r\nShows a summary of all active games, a per-galaxy table (list), or a specific galaxy. Defaults to 'all'.",
	}
	i.pregameCommands["help"] = Command{
		Handler: func(args []string, conn net.Conn) string {
			if len(args) == 0 || (len(args) > 0 && args[0] == "*") {
				keys := make([]string, 0, len(i.pregameCommands))
				for cmd := range i.pregameCommands {
					if cmd != "?" {
						keys = append(keys, cmd)
					}
				}
				sort.Strings(keys)
				var lines []string
				lines = append(lines, "Pregame commands:")
				for idx := 0; idx < len(keys); idx += 6 {
					end := idx + 6
					if end > len(keys) {
						end = len(keys)
					}
					row := keys[idx:end]
					padded := make([]string, 6)
					for j := 0; j < 6; j++ {
						if j < len(row) {
							padded[j] = fmt.Sprintf("%-13s", i.getAbbreviation(row[j], keys))
						} else {
							padded[j] = strings.Repeat(" ", 13)
						}
					}
					lines = append(lines, strings.Join(padded, ""))
				}
				return strings.Join(lines, "\r\n")
			}
			target := strings.ToLower(args[0])
			fullCmd, ok := i.resolveCommand(target, "pregame")
			if !ok {
				return "Invalid pregame command: " + target
			}
			return fmt.Sprintf("Command: %s\r\nDescription: %s", fullCmd, i.pregameCommands[fullCmd].Help)
		},
		Help: "Without parameter: list all GOWARS commands in 6 columns; with parameter: show detailed help for that command\r\n\r\n" +
			"Special characters:\r\n" +
			"Enter: (ASCII 13)   Submit command.\r\n" +
			"Backspace(ASCII 8)  Delete last character.\r\n" +
			"Ctrl+A (ASCII 1):   Move cursor to beginning of line.\r\n" +
			"Ctrl+B (ASCII 2):   Move cursor left.\r\n" +
			"Ctrl+C (ASCII 3):   Cancel command queue and interrupt output.\r\n" +
			"Ctrl+D (ASCII 4):   Signals end-of-file input (EOF).\r\n" +
			"Ctrl+E (ASCII 5):   Move cursor to end of line.\r\n" +
			"Ctrl+F (ASCII 6):   Move cursor right.\r\n" +
			"Ctrl+K (ASCII 11):  Delete to end of line.\r\n" +
			"Ctrl+L (ASCII 12):  Clears the terminal screen.\r\n" +
			// "Ctrl+S (ASCII 19): Halts terminal output (XOFF).\r\n" +
			// "Ctrl+Q (ASCII 17): Resumes terminal output (XON).\r\n" +
			"Ctrl+U (ASCII 21):  Clear entire line.\r\n" +
			"Ctrl+W (ASCII 23):  Delete last word (unsupported on web client)\r\n" +
			"Tab    (ASCII 9):   Command/parameter completion.\r\n" +
			"?      (ASCII 63):  Help and prompting.\r\n" +
			"Escape (ASCII 27):  Command completion or repeat last command.\r\n",
	}
	i.pregameCommands["?"] = Command{
		Handler: i.pregameCommands["help"].Handler,
		Help:    "Alias for 'help' in pregame",
	}

	// Gowars commands
	i.gowarsCommands["quit"] = Command{
		Handler: func(args []string, conn net.Conn) string {
			if info, ok := i.connections.Load(conn); ok {
				connInfo := info.(ConnectionInfo)
				// Capture the original galaxy before clearing it
				originalGalaxy := connInfo.Galaxy
				if connInfo.Ship != nil {
					// Set quit cooldown for the galaxy the ship is leaving
					i.setDestructionCooldownForConn(connInfo, originalGalaxy)
					i.cleanupShip(connInfo.Ship)
					// Refresh ship pointers for all connections after slice modification
					i.refreshShipPointers()
				}
				connInfo.Section = "pregame"
				connInfo.Shipname = ""
				connInfo.Ship = nil // Clear ship pointer when returning to pregame
				connInfo.Galaxy = 0
				connInfo.Prompt = "" // Clear custom prompt when returning to pregame
				connInfo.BaudRate = 0
				i.connections.Store(conn, connInfo)

				// Update galaxy tracker (use originalGalaxy, not the zeroed connInfo.Galaxy)
				i.trackerMutex.Lock()
				if tracker, exists := i.galaxyTracker[originalGalaxy]; exists {
					tracker.LastActive = time.Now()
					i.galaxyTracker[originalGalaxy] = tracker
				} else {
					now := time.Now()
					i.galaxyTracker[originalGalaxy] = GalaxyTracker{GalaxyStart: now, LastActive: now}
				}
				i.trackerMutex.Unlock()

				// Check galaxy 0 bases
				if i.checkGalaxyZeroBases() {
					i.regenerateGalaxyZero()
				}

				return "Returning to pregame section"
			}
			return "Error returning to pregame"
		},
		Help: "QUIT the game\r\n" +
			"Syntax: Quit\r\n" +
			"\r\n" +
			"Quit the game before normal end of execution and return to the\r\n" +
			"monitor. Your ship is released for use by another player, you're\r\n" +
			"chalked up as just one more casualty, and you can't CONTINUE the game.\r\n" +
			"If you want to rejoin the game, you'll have to wait 2 minutes, and\r\n" +
			"then either START or RUN the game. If you want to exit the game\r\n" +
			"temporarily (to answer SENDS, etc.), type ^C (CTL-C), and you'll\r\n" +
			"usually be able to CONTINUE. NOTE: If you're under red alert, you\r\n" +
			"won't be able to ^C out of the game; you'll have to use the QUIT\r\n" +
			"command.",
	}
	i.gowarsCommands["users"] = Command{
		Handler: func(args []string, conn net.Conn) string {
			// Find current galaxy
			var currentGalaxy uint16 = 0
			outputShort := false
			if info, ok := i.connections.Load(conn); ok {
				currentGalaxy = info.(ConnectionInfo).Galaxy
				if info.(ConnectionInfo).OutputState == "short" {
					outputShort = true
				}
			}
			var lines []string
			if outputShort {
				lines = append(lines, " Ship            Captain        Speed")
				lines = append(lines, strings.Repeat("-", 37))
			} else {
				lines = append(lines, " Ship            Captain        Speed 	Connection Info")
				lines = append(lines, strings.Repeat("-", 55))
			}

			seenShips := make(map[string]bool)
			i.connections.Range(func(_, value interface{}) bool {
				info := value.(ConnectionInfo)
				if info.Galaxy != currentGalaxy {
					return true
				}
				shipKey := info.Shipname
				if shipKey == "" {
					return true // skip users with no shipname
				}
				if seenShips[shipKey] {
					return true // already listed this ship
				}
				seenShips[shipKey] = true

				var shipnameStr string
				if info.AdminMode == true {
					shipnameStr = fmt.Sprintf("*")
				} else {
					shipnameStr = fmt.Sprintf(" ")
				}

				shipnameStr = shipnameStr + fmt.Sprintf("%-16s", info.Shipname)
				usernameStr := fmt.Sprintf("%-16s", info.Name)
				speedStr := fmt.Sprintf("%d", info.BaudRate)
				if outputShort {
					lines = append(lines, fmt.Sprintf("%s%s%s", shipnameStr, usernameStr, speedStr))
				} else {
					connInfoStr := fmt.Sprintf("%s:%s", info.IP, info.Port)
					lines = append(lines, fmt.Sprintf("%s%s%s\t%5s", shipnameStr, usernameStr, speedStr, connInfoStr))
				}
				return true
			})
			return strings.Join(lines, "\r\n")
		},
		Help: "List USERS\r\n" +
			"Syntax: Users\r\n" +
			"\r\n" +
			"List all ships currently in the game. Include ship name, captain (may\r\n" +
			"be changed by SET NAME), TTY speed, PPN, TTY number, and job number.\r\n" +
			"If the output format is set to medium or short, omit the TTY and job\r\n" +
			"numbers. If the output format is set to short, omit the TTY speed and\r\n" +
			"PPN (include only the ship name and captain).",
	}
	i.gowarsCommands["repair"] = Command{
		Handler: func(args []string, conn net.Conn) string {
			var galaxy uint16

			// Find the user's ship
			info, ok := i.connections.Load(conn)
			if !ok || info.(ConnectionInfo).Section != "gowars" || info.(ConnectionInfo).Shipname == "" {
				return "You must be in GOWARS with a ship to use this command"
			}
			connInfo := info.(ConnectionInfo)
			shipname := connInfo.Shipname
			galaxy = connInfo.Galaxy

			var ship *Object
			ship = i.getShipByName(galaxy, shipname)
			if ship == nil {
				return "Error: ship not found"
			}

			// Determine dock status and set repair parameters per new spec:
			//   Not docked: default -50 per device
			//   Docked:     default -100 per device
			docked := strings.Contains(strings.ToLower(ship.Condition), "docked")
			var defaultRepair int
			if docked {
				defaultRepair = 100 // 100 * 100 = 10000 units per device (1000.0 displayed)
			} else {
				defaultRepair = 50 // 50 * 100 = 5000 units per device (500.0 displayed)
			}

			// List of device damage fields to repair
			deviceFields := []*int{
				&ship.ShieldsDamage,
				&ship.WarpEnginesDamage,
				&ship.ImpulseEnginesDamage,
				&ship.TorpedoTubeDamage,
				&ship.PhasersDamage,
				&ship.ComputerDamage,
				&ship.LifeSupportDamage,
				&ship.RadioDamage,
				&ship.TractorDamage,
			}
			deviceNames := []string{
				"Shields", "Warp Engines", "Impulse Engines", "Torpedo Tubes", "Phasers", "Computer", "Life Support", "Radio", "Tractor Beam",
			}

			// Find maximum damage across all devices
			maxDamage := 0
			for _, field := range deviceFields {
				if *field > maxDamage {
					maxDamage = *field
				}
			}
			if maxDamage == 0 {
				return "No damaged devices to repair."
			}

			// Parse arguments: either a number N (repair N*100 units per device) or "ALL" (repair all damage)
			repairAmount := defaultRepair * 100
			if len(args) > 0 {
				if strings.ToUpper(args[0]) == "ALL" {
					repairAmount = maxDamage
				} else {
					val, err := strconv.Atoi(args[0])
					if err != nil || val <= 0 {
						return "Usage: repair [units|ALL] (units must be a positive integer)"
					}
					repairAmount = val * 100
				}
			}

			// Cap repairAmount to actual maximum damage (no point repairing more than needed)
			if repairAmount > maxDamage {
				repairAmount = maxDamage
			}

			// No energy cost for repair (per new table)
			// Apply repairs: subtract repairAmount from each damaged device, floor at 0
			var repaired []string
			for idx, field := range deviceFields {
				before := *field
				if before > 0 {
					*field -= repairAmount
					if *field < 0 {
						*field = 0
					}
					after := *field
					if after < before {
						repaired = append(repaired, fmt.Sprintf("%s: %d → %d", deviceNames[idx], before, after))
					}
				}
			}

			// Apply time delay: 100ms per unit repaired, but cap at 500ms max
			repairTime := repairAmount * 10
			if repairTime > 500 {
				repairTime = 500
			}
			var shipConn net.Conn
			i.connections.Range(func(key, value interface{}) bool {
				ci := value.(ConnectionInfo)
				if ci.Shipname == ship.Name && ci.Galaxy == galaxy {
					shipConn = key.(net.Conn)
					return false
				}
				return true
			})
			i.delayPause(shipConn, repairTime, galaxy, ship.Type, ship.Side)

			// Build output message
			msg := "\r\n"
			return msg
		},
		Help: "REPAIR device damage\r\n" +
			"Syntax: REpair [<units>|ALL]\r\n" +
			"\r\n" +
			"Repair damaged ship devices. If a ship suffers a critical hit to a\r\n" +
			"device, REPAIR can be used to restore the device to full (or partial)\r\n" +
			"working order. A REPAIR removes the specified units of damage from\r\n" +
			"each damaged device. If a number N is specified, N*100 units of damage are\r\n" +
			"repaired per device. If ALL is specified, all damage is fully repaired.\r\n" +
			"If the ship is DOCKED, the default repair is 100 (10000 units) per device. If not docked, the default is 50 (5000 units) per device.\r\n" +
			"REPAIR does NOT reduce the SHIP hull damage.\r\n" +
			"\r\n" +
			"Examples:\r\n" +
			"RE                      Repair 500 units per device (not docked) or 1000 (docked).\r\n" +
			"RE 20                   Repair 2000 units of device damage per device.\r\n" +
			"RE ALL                  Fully repair all damaged devices.",
	}

	i.gowarsCommands["tell"] = Command{
		Handler: func(args []string, conn net.Conn) string {
			if len(args) == 0 {
				return "Error: tell requires a target and message:\r\ntell Vulcan hello\r\ntell all Lets fight\r\ntell federation enemy is at 38-48\r\ntell 39750 Lets play in galaxy 3!"
			}

			senderInfo, ok := i.connections.Load(conn)
			if !ok {
				return "Error: connection not found"
			}
			sender := senderInfo.(ConnectionInfo)

			// Determine sender identity
			senderName := sender.Shipname
			if senderName == "" {
				// In pregame mode, use username or connection info
				if sender.Name != "" {
					senderName = sender.Name
				} else {
					senderName = sender.Port
				}
			}

			// Define valid optional parameters
			validParams := map[string]bool{
				"all":        true,
				"federation": true,
				"human":      true,
				"empire":     true,
				"klingon":    true,
				"enemy":      true,
				"friendly":   true,
			}

			targetStr := args[0]
			messageStart := 1

			// Check if first argument is an optional parameter
			if param, ok := i.resolveParameter(strings.ToLower(targetStr), validParams); ok {
				if len(args) < 2 {
					return fmt.Sprintf("Error: tell %s requires a message", param)
				}

				// Handle optional parameters with stubs
				message := strings.Join(args[1:], " ")
				switch param {
				case "all":
					// Send message to all users with radios ON (limited to same galaxy when in game)
					messagesSent := 0
					i.connections.Range(func(key, value interface{}) bool {
						connKey := key.(net.Conn)
						connInfo := value.(ConnectionInfo)
						if connKey != conn { // Don't send to sender
							// When sender is in gowars mode, only send to players in the same galaxy
							if sender.Section == "gowars" {
								if connInfo.Section != "gowars" || connInfo.Galaxy != sender.Galaxy {
									return true // Skip players not in the same galaxy
								}
							}
							// In pregame mode, don't check radio status, but in gowars mode, check radio
							skipUser := false
							if connInfo.Section == "gowars" {
								if connInfo.Ship != nil && !connInfo.Ship.RadioOnOff {
									skipUser = true
								}
							}
							if skipUser {
								return true // Skip ships with radio off
							}
							if writerRaw, ok := i.writers.Load(connKey); ok {
								writer := writerRaw.(*bufio.Writer)
								if mutexRaw, ok := i.writerMutexs.Load(connKey); ok {
									mutex := mutexRaw.(*sync.Mutex)
									mutex.Lock()
									if strings.HasPrefix(senderName, "Romulan") {
										senderName = "Romulan"
									}
									fmt.Fprintf(writer, "\r\nmessage from %s: %s\r\n", senderName, message)
									writer.Flush()
									mutex.Unlock()
									messagesSent++
								}
							}
						}
						return true
					})

					// Update galaxy tracker (only if in gowars mode)
					if sender.Section == "gowars" {
						i.trackerMutex.Lock()
						if tracker, exists := i.galaxyTracker[sender.Galaxy]; exists {
							tracker.LastActive = time.Now()
							i.galaxyTracker[sender.Galaxy] = tracker
						} else {
							now := time.Now()
							i.galaxyTracker[sender.Galaxy] = GalaxyTracker{GalaxyStart: now, LastActive: now}
						}
						i.trackerMutex.Unlock()
					}

					return fmt.Sprintf("Message sent to %d users", messagesSent)
				case "federation":
					// Send message to all federation users with radios ON (limited to same galaxy)
					messagesSent := 0
					i.connections.Range(func(key, value interface{}) bool {
						connKey := key.(net.Conn)
						connInfo := value.(ConnectionInfo)
						if connKey != conn && connInfo.Section == "gowars" && connInfo.Ship != nil && connInfo.Galaxy == sender.Galaxy {
							// Check if this user's ship is federation and radio is on
							if connInfo.Ship.Side == "federation" && connInfo.Ship.RadioOnOff {
								if writerRaw, ok := i.writers.Load(connKey); ok {
									writer := writerRaw.(*bufio.Writer)
									if mutexRaw, ok := i.writerMutexs.Load(connKey); ok {
										mutex := mutexRaw.(*sync.Mutex)
										mutex.Lock()
										if strings.HasPrefix(senderName, "Romulan") {
											senderName = "Romulan"
										}
										fmt.Fprintf(writer, "\r\nmessage from %s: %s\r\n", senderName, message)
										writer.Flush()
										mutex.Unlock()
										messagesSent++
									}
								}
							}
						}
						return true
					})
					return fmt.Sprintf("Message sent to %d federation users", messagesSent)
				case "human":
					// Send message to all human players (federation + empire) with radios ON (limited to same galaxy)
					messagesSent := 0
					i.connections.Range(func(key, value interface{}) bool {
						connKey := key.(net.Conn)
						connInfo := value.(ConnectionInfo)
						if connKey != conn && connInfo.Section == "gowars" && connInfo.Ship != nil && connInfo.Galaxy == sender.Galaxy {
							// Check if this user's ship is federation or empire and radio is on
							if (connInfo.Ship.Side == "federation" || connInfo.Ship.Side == "empire") && connInfo.Ship.RadioOnOff {
								if writerRaw, ok := i.writers.Load(connKey); ok {
									writer := writerRaw.(*bufio.Writer)
									if mutexRaw, ok := i.writerMutexs.Load(connKey); ok {
										mutex := mutexRaw.(*sync.Mutex)
										mutex.Lock()
										if strings.HasPrefix(senderName, "Romulan") {
											senderName = "Romulan"
										}
										fmt.Fprintf(writer, "\r\nmessage from %s: %s\r\n", senderName, message)
										writer.Flush()
										mutex.Unlock()
										messagesSent++
									}
								}
							}
						}
						return true
					})
					return fmt.Sprintf("Message sent to %d human players", messagesSent)
				case "empire":
					// Send message to all empire users with radios ON (limited to same galaxy)
					messagesSent := 0
					i.connections.Range(func(key, value interface{}) bool {
						connKey := key.(net.Conn)
						connInfo := value.(ConnectionInfo)
						if connKey != conn && connInfo.Section == "gowars" && connInfo.Ship != nil && connInfo.Galaxy == sender.Galaxy {
							// Check if this user's ship is empire and radio is on
							if connInfo.Ship.Side == "empire" && connInfo.Ship.RadioOnOff {
								if writerRaw, ok := i.writers.Load(connKey); ok {
									writer := writerRaw.(*bufio.Writer)
									if mutexRaw, ok := i.writerMutexs.Load(connKey); ok {
										mutex := mutexRaw.(*sync.Mutex)
										mutex.Lock()
										if strings.HasPrefix(senderName, "Romulan") {
											senderName = "Romulan"
										}
										fmt.Fprintf(writer, "\r\nmessage from %s: %s\r\n", senderName, message)
										writer.Flush()
										mutex.Unlock()
										messagesSent++
									}
								}
							}
						}
						return true
					})
					return fmt.Sprintf("Message sent to %d empire users", messagesSent)
				case "klingon":
					// Send message to all empire/klingon users with radios ON (limited to same galaxy)
					// Klingon is an alias for empire
					messagesSent := 0
					i.connections.Range(func(key, value interface{}) bool {
						connKey := key.(net.Conn)
						connInfo := value.(ConnectionInfo)
						if connKey != conn && connInfo.Section == "gowars" && connInfo.Ship != nil && connInfo.Galaxy == sender.Galaxy {
							if connInfo.Ship.Side == "empire" && connInfo.Ship.RadioOnOff {
								if writerRaw, ok := i.writers.Load(connKey); ok {
									writer := writerRaw.(*bufio.Writer)
									if mutexRaw, ok := i.writerMutexs.Load(connKey); ok {
										mutex := mutexRaw.(*sync.Mutex)
										mutex.Lock()
										if strings.HasPrefix(senderName, "Romulan") {
											senderName = "Romulan"
										}
										fmt.Fprintf(writer, "\r\nmessage from %s: %s\r\n", senderName, message)
										writer.Flush()
										mutex.Unlock()
										messagesSent++
									}
								}
							}
						}
						return true
					})
					return fmt.Sprintf("Message sent to %d klingon users", messagesSent)
				case "enemy":
					// Send message to all enemy users (not on sender's side) with radios ON
					// Only works in gowars mode
					if sender.Section != "gowars" {
						return "Error: enemy parameter only works in gowars mode"
					}
					senderSide, ok := i.getShipSide(conn)
					if !ok {
						return "Error: unable to determine your side"
					}
					messagesSent := 0
					i.connections.Range(func(key, value interface{}) bool {
						connKey := key.(net.Conn)
						connInfo := value.(ConnectionInfo)
						if connKey != conn && connInfo.Section == "gowars" && connInfo.Ship != nil && connInfo.Galaxy == sender.Galaxy {
							// Check if this user's ship is not on sender's side and not neutral and radio is on
							if connInfo.Ship.Side != senderSide && connInfo.Ship.Side != "neutral" && connInfo.Ship.RadioOnOff {
								if writerRaw, ok := i.writers.Load(connKey); ok {
									writer := writerRaw.(*bufio.Writer)
									if mutexRaw, ok := i.writerMutexs.Load(connKey); ok {
										mutex := mutexRaw.(*sync.Mutex)
										mutex.Lock()
										if strings.HasPrefix(senderName, "Romulan") {
											senderName = "Romulan"
										}
										if strings.HasPrefix(senderName, "Romulan") {
											senderName = "Romulan"
										}
										fmt.Fprintf(writer, "\r\nmessage from %s: %s\r\n", senderName, message)
										writer.Flush()
										mutex.Unlock()
										messagesSent++
									}
								}
							}
						}
						return true
					})
					return fmt.Sprintf("Message sent to %d enemy users", messagesSent)
				case "friendly":
					// Send message to all friendly users (on sender's side) with radios ON
					// Only works in gowars mode
					if sender.Section != "gowars" {
						return "Error: friendly parameter only works in gowars mode"
					}
					senderSide, ok := i.getShipSide(conn)
					if !ok {
						return "Error: unable to determine your side"
					}
					messagesSent := 0
					i.connections.Range(func(key, value interface{}) bool {
						connKey := key.(net.Conn)
						connInfo := value.(ConnectionInfo)
						if connKey != conn && connInfo.Section == "gowars" && connInfo.Ship != nil && connInfo.Galaxy == sender.Galaxy {
							// Check if this user's ship is on sender's side and radio is on
							if connInfo.Ship.Side == senderSide && connInfo.Ship.RadioOnOff {
								if writerRaw, ok := i.writers.Load(connKey); ok {
									writer := writerRaw.(*bufio.Writer)
									if mutexRaw, ok := i.writerMutexs.Load(connKey); ok {
										mutex := mutexRaw.(*sync.Mutex)
										mutex.Lock()
										fmt.Fprintf(writer, "\r\nmessage from %s: %s\r\n", senderName, message)
										writer.Flush()
										mutex.Unlock()
										messagesSent++
									}
								}
							}
						}
						return true
					})
					return fmt.Sprintf("Message sent to %d friendly users", messagesSent)
				}
			}

			// Handle parameter completion
			for _, arg := range args {
				if strings.HasSuffix(arg, "?") {
					prefix := strings.ToLower(strings.TrimSuffix(arg, "?"))
					var matches []string

					if sender.Section == "gowars" {
						// In gowars mode: show optional parameters and shipnames, but NOT connections
						for param := range validParams {
							if strings.HasPrefix(param, prefix) {
								matches = append(matches, param)
							}
						}

						// Check active shipnames in same galaxy
						i.connections.Range(func(_, value interface{}) bool {
							info := value.(ConnectionInfo)
							if info.Section == "gowars" && info.Galaxy == sender.Galaxy && info.Shipname != "" && strings.HasPrefix(strings.ToLower(info.Shipname), prefix) {
								matches = append(matches, info.Shipname)
							}
							return true
						})
					} else {
						// In pregame mode: show connections only (usernames/IPs)
						i.connections.Range(func(_, value interface{}) bool {
							info := value.(ConnectionInfo)
							if info.Name != "" && strings.HasPrefix(strings.ToLower(info.Name), prefix) {
								matches = append(matches, info.Name)
							}
							return true
						})
					}

					if len(matches) == 0 {
						return "Error: No valid completion"
					}
					return "tell " + strings.Join(matches, " | ")
				}
			}

			// Original direct target functionality (shipname, port, or username)
			if len(args) < 2 {
				return "Error: tell requires a target (shipname/port/username) and message (e.g., tell ship1 hello)"
			}

			message := strings.Join(args[messageStart:], " ")
			targetFound := false
			selfExcluded := false
			var abbrevMatches []struct {
				key  interface{}
				info ConnectionInfo
			}

			i.connections.Range(func(key, value interface{}) bool {
				info := value.(ConnectionInfo)
				// Restrict direct shipname/port/name match to sender's galaxy in gowars mode
				if info.Section == "gowars" && info.Shipname != "" && info.Galaxy != sender.Galaxy {
					return true
				}
				if info.Shipname == targetStr || info.Port == targetStr || info.Name == targetStr {
					// Check if the target is the sender's own ship or connection
					if (info.Shipname != "" && info.Shipname == sender.Shipname && info.Galaxy == sender.Galaxy) ||
						(info.Port != "" && info.Port == sender.Port) ||
						(info.Name != "" && info.Name == sender.Name) {
						targetFound = true
						selfExcluded = true
						return false // Stop searching, but don't send the message
					}
					// Check radio status only if in gowars mode
					if info.Section == "gowars" {
						radioOn := false
						ship := i.getShipByName(info.Galaxy, info.Shipname)
						if ship != nil {
							radioOn = ship.RadioOnOff
						}
						if !radioOn {
							return false // Target found, but radio is off, do not send
						}
					}
					targetFound = true
					connKey := key.(net.Conn)
					if writerRaw, ok := i.writers.Load(connKey); ok {
						writer := writerRaw.(*bufio.Writer)
						if mutexRaw, ok := i.writerMutexs.Load(connKey); ok {
							mutex := mutexRaw.(*sync.Mutex)
							mutex.Lock()
							if strings.HasPrefix(senderName, "Romulan") {
								senderName = "Romulan"
							}
							if strings.HasPrefix(senderName, "Romulan") {
								senderName = "Romulan"
							}
							fmt.Fprintf(writer, "\r\nmessage from %s: %s\r\n", senderName, message)
							writer.Flush()
							mutex.Unlock()
						}
					}
					return false
				}
				// Collect abbreviation matches (only in gowars mode, only shipnames, only same galaxy)
				if info.Section == "gowars" && info.Shipname != "" &&
					info.Galaxy == sender.Galaxy &&
					strings.HasPrefix(strings.ToLower(info.Shipname), strings.ToLower(targetStr)) {
					abbrevMatches = append(abbrevMatches, struct {
						key  interface{}
						info ConnectionInfo
					}{key, info})
				}
				return true
			})

			if !targetFound {
				if len(abbrevMatches) == 1 {
					// Check if the abbreviation match is the sender's own ship
					info := abbrevMatches[0].info
					if info.Shipname != "" && info.Shipname == sender.Shipname && info.Galaxy == sender.Galaxy {
						return "Self excluded from message."
					}
					connKey := abbrevMatches[0].key.(net.Conn)
					// Check radio status only if in gowars mode
					if info.Section == "gowars" {
						radioOn := false
						ship := i.getShipByName(info.Galaxy, info.Shipname)
						if ship != nil {
							radioOn = ship.RadioOnOff
						}
						if !radioOn {
							return fmt.Sprintf("Error: target ship '%s' radio is off", info.Shipname)
						}
					}
					if writerRaw, ok := i.writers.Load(connKey); ok {
						writer := writerRaw.(*bufio.Writer)
						if mutexRaw, ok := i.writerMutexs.Load(connKey); ok {
							mutex := mutexRaw.(*sync.Mutex)
							mutex.Lock()
							fmt.Fprintf(writer, "\r\nmessage from %s: %s\r\n", senderName, message)
							writer.Flush()
							mutex.Unlock()
						}
					}
					// Update galaxy tracker (only if in gowars mode)
					if sender.Section == "gowars" {
						i.trackerMutex.Lock()
						if tracker, exists := i.galaxyTracker[sender.Galaxy]; exists {
							tracker.LastActive = time.Now()
							i.galaxyTracker[sender.Galaxy] = tracker
						} else {
							now := time.Now()
							i.galaxyTracker[sender.Galaxy] = GalaxyTracker{GalaxyStart: now, LastActive: now}
						}
						i.trackerMutex.Unlock()
					}
					return fmt.Sprintf("Message sent to %s", info.Shipname)
				} else if len(abbrevMatches) > 1 {
					// Ambiguous abbreviation
					var names []string
					for _, m := range abbrevMatches {
						names = append(names, m.info.Shipname)
					}
					return fmt.Sprintf("Error: abbreviation '%s' matches multiple ships: %s", targetStr, strings.Join(names, ", "))
				} else {
					return fmt.Sprintf("Error: no active player found with shipname, port, or username '%s'", targetStr)
				}
			}
			if selfExcluded {
				return "Self excluded from message."
			}

			// Update galaxy tracker (only if in gowars mode)
			if sender.Section == "gowars" {
				i.trackerMutex.Lock()
				if tracker, exists := i.galaxyTracker[sender.Galaxy]; exists {
					tracker.LastActive = time.Now()
					i.galaxyTracker[sender.Galaxy] = tracker
				} else {
					now := time.Now()
					i.galaxyTracker[sender.Galaxy] = GalaxyTracker{GalaxyStart: now, LastActive: now}
				}
				i.trackerMutex.Unlock()
			}

			return fmt.Sprintf("Message sent to %s", targetStr)
		},
		Help: "TELL another ship something using the sub-space radio\r\n" +
			"Syntax: TEll All|FEderation|HUman|EMpire|Klingon|ENemy|FRiendly|\r\n" +
			"<ship names>;<msg>\r\n" +
			"\r\n" +
			"Send messages to one or several of the players currently in the game,\r\n" +
			"with no range limitation. Players who have turned their radios off,\r\n" +
			"or have a critically damaged sub-space radio can not be sent to. The\r\n" +
			"TELL command can not be repeated using the ESCAPE key (no junk mail!).\r\n" +
			"\r\n" +
			"Examples:\r\n" +
			"TE V;Hello!             Send \"Hello!\" to the Vulcan.\r\n" +
			"TE KL;DROP DEAD         Send \"DROP DEAD\" to all Klingons.\r\n" +
			"TE V,E;HELP ME          Send \"HELP ME\" to the Vulcan and Excalibur."}

	i.gowarsCommands["summary"] = Command{
		Handler: func(args []string, conn net.Conn) string {
			if len(args) > 0 && (args[0] == "?" || args[0] == "help") {
				return "Subcommands: bases, enemy, friendly, planets, ships"
			}
			// Optional parameter stubs with abbreviation support
			if len(args) >= 1 {
				validParams := map[string]bool{
					"ships":    true,
					"bases":    true,
					"planets":  true,
					"friendly": true,
					"enemy":    true,
				}
				if resolved, ok := i.resolveParameter(strings.ToLower(args[0]), validParams); ok {
					switch resolved {
					case "ships":
						// Implement actual logic: print number of federation ships and number of empire ships in current galaxy
						var galaxy uint16 = 0
						if info, ok := i.connections.Load(conn); ok {
							galaxy = info.(ConnectionInfo).Galaxy
						}
						federationShips := 0
						empireShips := 0
						ships := i.getObjectsByType(galaxy, "Ship")
						if ships != nil {
							for _, ship := range ships {
								if ship.Side == "federation" {
									federationShips++
								} else if ship.Side == "empire" {
									empireShips++
								}
							}
						}
						return fmt.Sprintf("Federation ships: %d\r\nEmpire ships: %d", federationShips, empireShips)
					case "bases":
						// Implement actual logic: print number of federation bases and number of enemy bases in current galaxy
						var galaxy uint16 = 0
						if info, ok := i.connections.Load(conn); ok {
							galaxy = info.(ConnectionInfo).Galaxy
						}
						federationBases := 0
						empireBases := 0
						bases := i.getObjectsByType(galaxy, "Base")
						if bases != nil {
							for _, base := range bases {
								if base.Side == "federation" {
									federationBases++
								} else if base.Side == "empire" {
									empireBases++
								}
							}
						}
						return fmt.Sprintf("Federation bases: %d\r\nEmpire bases: %d", federationBases, empireBases)
					case "planets":
						// Implement actual logic: print number of federation planets, empire planets, and neutral planets in current galaxy
						var galaxy uint16 = 0
						if info, ok := i.connections.Load(conn); ok {
							galaxy = info.(ConnectionInfo).Galaxy
						}
						federationPlanets := 0
						empirePlanets := 0
						neutralPlanets := 0
						planets := i.getObjectsByType(galaxy, "Planet")
						if planets != nil {
							for _, planet := range planets {
								if planet.Side == "federation" {
									federationPlanets++
								} else if planet.Side == "empire" {
									empirePlanets++
								} else if planet.Side == "neutral" {
									neutralPlanets++
								}
							}
						}
						return fmt.Sprintf("%d Federation planets in game\r\n%d Empire planets in game\r\n%d Neutral planets in game", federationPlanets, empirePlanets, neutralPlanets)
					case "friendly":
						// Implement actual logic: print the number of planets, bases, and ships that are on your side in the current galaxy
						var galaxy uint16 = 0
						var side string
						if info, ok := i.connections.Load(conn); ok {
							galaxy = info.(ConnectionInfo).Galaxy
							if info.(ConnectionInfo).Shipname != "" {
								ship := i.getShipByName(galaxy, info.(ConnectionInfo).Shipname)
								if ship != nil {
									side = ship.Side
								}
							}
						}
						if side == "" {
							return "Error: unable to determine your side"
						}
						planets := 0
						bases := 0
						ships := 0

						// Count bases using optimized approach
						basesObjs := i.getObjectsByType(galaxy, "Base")
						if basesObjs != nil {
							for _, obj := range basesObjs {
								if obj.Side == side {
									bases++
								}
							}
						}

						// Count planets using optimized approach
						planetsObjs := i.getObjectsByType(galaxy, "Planet")
						if planetsObjs != nil {
							for _, obj := range planetsObjs {
								if obj.Side == side {
									planets++
								}
							}
						}

						// Count ships using optimized approach
						shipsObjs := i.getObjectsByType(galaxy, "Ship")
						if shipsObjs != nil {
							for _, obj := range shipsObjs {
								if obj.Side == side {
									ships++
								}
							}
						}
						return fmt.Sprintf("Friendly planets: %d\r\nFriendly bases: %d\r\nFriendly ships: %d", planets, bases, ships)
					case "enemy":
						// Implement actual logic: print the number of planets, bases, and ships that are NOT on your side in the current galaxy
						var galaxy uint16 = 0
						var side string
						if info, ok := i.connections.Load(conn); ok {
							galaxy = info.(ConnectionInfo).Galaxy
							if info.(ConnectionInfo).Shipname != "" {
								ship := i.getShipByName(galaxy, info.(ConnectionInfo).Shipname)
								if ship != nil {
									side = ship.Side
								}
							}
						}
						if side == "" {
							return "Error: unable to determine your side"
						}
						planets := 0
						bases := 0
						ships := 0

						// Count bases using optimized approach
						basesObjs := i.getObjectsByType(galaxy, "Base")
						if basesObjs != nil {
							for _, obj := range basesObjs {
								if obj.Side != side {
									bases++
								}
							}
						}

						// Count planets using optimized approach
						planetsObjs := i.getObjectsByType(galaxy, "Planet")
						if planetsObjs != nil {
							for _, obj := range planetsObjs {
								if obj.Side != side {
									planets++
								}
							}
						}

						// Count ships using optimized approach
						shipsObjs := i.getObjectsByType(galaxy, "Ship")
						if shipsObjs != nil {
							for _, obj := range shipsObjs {
								if obj.Side != side {
									ships++
								}
							}
						}
						return fmt.Sprintf("Enemy planets: %d\r\nEnemy bases: %d\r\nEnemy ships: %d", planets, bases, ships)
					}
				}
			}
			// Get current user's galaxy
			var currentGalaxy uint16 = 0
			if info, ok := i.connections.Load(conn); ok {
				currentGalaxy = info.(ConnectionInfo).Galaxy
			}

			// Count users in current galaxy
			usersInGalaxy := 0
			i.connections.Range(func(key, value interface{}) bool {
				if connInfo, ok := value.(ConnectionInfo); ok {
					if connInfo.Galaxy == currentGalaxy {
						usersInGalaxy++
					}
				}
				return true
			})

			// Compute object stats for current galaxy only
			stats := &galaxyStats{}

			// Count bases using optimized approach
			bases := i.getObjectsByType(currentGalaxy, "Base")
			if bases != nil {
				for _, obj := range bases {
					if obj.Side == "federation" {
						stats.FederationBases++
					} else if obj.Side == "empire" {
						stats.EmpireBases++
					}
				}
			}

			// Count planets using optimized approach
			planets := i.getObjectsByType(currentGalaxy, "Planet")
			if planets != nil {
				for _, obj := range planets {
					switch obj.Side {
					case "neutral":
						stats.NeutralPlanets++
					case "federation":
						stats.FederationPlanets++
					case "empire":
						stats.EmpirePlanets++
					}
				}
			}

			// Count other object types using optimized approach
			blackHoles := i.getObjectsByType(currentGalaxy, "Black Hole")
			if blackHoles != nil {
				stats.BlackHoles = len(blackHoles)
			}

			stars := i.getObjectsByType(currentGalaxy, "Star")
			if stars != nil {
				stats.Stars = len(stars)
			}

			ships := i.getObjectsByType(currentGalaxy, "Ship")
			if ships != nil {
				stats.Ships = len(ships)
			}

			// Build output for current galaxy only
			var lines []string
			lines = append(lines, fmt.Sprintf("Galaxy %d Summary:", currentGalaxy))

			lines = append(lines, fmt.Sprintf("  Users in galaxy: %d", usersInGalaxy))
			lines = append(lines, fmt.Sprintf("  Federation Bases: %d", stats.FederationBases))
			lines = append(lines, fmt.Sprintf("  Empire Bases: %d", stats.EmpireBases))
			lines = append(lines, fmt.Sprintf("  Black Holes: %d", stats.BlackHoles))
			lines = append(lines, fmt.Sprintf("  Neutral Planets: %d", stats.NeutralPlanets))
			lines = append(lines, fmt.Sprintf("  Federation Planets: %d", stats.FederationPlanets))
			lines = append(lines, fmt.Sprintf("  Empire Planets: %d", stats.EmpirePlanets))
			lines = append(lines, fmt.Sprintf("  Stars: %d", stats.Stars))
			lines = append(lines, fmt.Sprintf("  Ships: %d", stats.Ships))

			// Update galaxy tracker
			if info, ok := i.connections.Load(conn); ok {
				connInfo := info.(ConnectionInfo)
				i.trackerMutex.Lock()
				if tracker, exists := i.galaxyTracker[connInfo.Galaxy]; exists {
					tracker.LastActive = time.Now()
					i.galaxyTracker[connInfo.Galaxy] = tracker
				} else {
					now := time.Now()
					i.galaxyTracker[connInfo.Galaxy] = GalaxyTracker{GalaxyStart: now, LastActive: now}
				}
				i.trackerMutex.Unlock()
			}

			return strings.Join(lines, "\r\n")
		},
		Help: "Give SUMMARY on number of ships, bases, and planets\r\n" +
			"Syntax: SUmmary [<keywords>]\r\n" +
			"\r\n" +
			"Give any of the information available from the LIST command, but give\r\n" +
			"only a summary by default. See the help on LIST for more information\r\n" +
			"and the complete set of keywords that can be used to modify SUMMARY\r\n" +
			"output.\r\n" +
			"\r\n" +
			"Examples:\r\n" +
			"SUM                     Tell how many ships, bases, and planets are in the\r\n" +
			"                        game (broken down into friendly, enemy, and neutral\r\n" +
			"                        categories).\r\n" +
			"SUM EN                  Tell how many enemies are in the game (number of\r\n" +
			"                        Romulans, enemy ships, enemy bases, and enemy\r\n" +
			"                        planets).",
	}
	i.gowarsCommands["list"] = Command{
		Handler: func(args []string, conn net.Conn) string {
			info, ok := i.connections.Load(conn)
			if !ok || info.(ConnectionInfo).Shipname == "" {
				return "Error: you must be in GOWARS with a shipname to use list"
			}
			connInfo := info.(ConnectionInfo)
			senderSide, ok := i.getShipSide(conn)
			if !ok {
				return "Error: unable to determine your side"
			}
			senderX, senderY, ok := i.getShipLocation(conn)
			if !ok {
				return "Error: unable to determine your location"
			}

			keywords := []string{}
			if len(args) > 0 {
				allArgs := strings.Join(args, " ")
				keywords = strings.Fields(allArgs)
			}
			validKeywords := map[string]bool{
				"neutral":  true,
				"friendly": true,
				"enemy":    true,
				"closest":  true,
				"ships":    true,
				"bases":    true,
				"planets":  true,
				//				"blackholes": true,
				"ports":      true,
				"human":      true,
				"empire":     true,
				"federation": true,
				"targets":    true,
				"captured":   true,
				"summary":    true,
			}
			validClosestTypes := map[string]bool{
				"base":     true,
				"enemy":    true,
				"friendly": true,
				"neutral":  true,
				"planet":   true,
				//				"star":      true,
				"ship": true,
				//				"blackhole": true,
				"ports":      true,
				"human":      true,
				"empire":     true,
				"federation": true,
				"targets":    true,
				"captured":   true,
			}

			// Resolve keyword abbreviations
			resolvedKeywords := make([]string, 0, len(keywords))
			for idx, kw := range keywords {
				if idx == 0 {
					// First keyword: resolve against validKeywords
					if fullKW, ok := i.resolveParameter(kw, validKeywords); ok {
						resolvedKeywords = append(resolvedKeywords, fullKW)
					} else {
						resolvedKeywords = append(resolvedKeywords, kw)
					}
				} else if idx == 1 && len(resolvedKeywords) > 0 && resolvedKeywords[0] == "closest" {
					// Second keyword after "closest": resolve against validClosestTypes
					if fullKW, ok := i.resolveParameter(kw, validClosestTypes); ok {
						resolvedKeywords = append(resolvedKeywords, fullKW)
					} else {
						resolvedKeywords = append(resolvedKeywords, kw)
					}
				} else {
					// Other keywords: resolve against validKeywords
					if fullKW, ok := i.resolveParameter(kw, validKeywords); ok {
						resolvedKeywords = append(resolvedKeywords, fullKW)
					} else {
						resolvedKeywords = append(resolvedKeywords, kw)
					}
				}
			}

			// "list captured": Output all non-neutral planets within range of all centers (your ship and friendly ships with radio on)
			if len(resolvedKeywords) > 0 && resolvedKeywords[0] == "captured" {
				// Find all centers: your ship and friendly ships with radio on
				var centers []struct{ X, Y int }
				centers = append(centers, struct{ X, Y int }{X: senderX, Y: senderY})
				// Get ships from objectsByType and filter by side/radio
				if ships := i.getObjectsByType(connInfo.Galaxy, "Ship"); ships != nil {
					for _, ship := range ships {
						if ship.Side == senderSide && ship.RadioOnOff && ship.Name != connInfo.Shipname {
							centers = append(centers, struct{ X, Y int }{X: ship.LocationX, Y: ship.LocationY})
						}
					}
				}
				if len(centers) == 0 {
					return "No valid centers (your ship or friendly ships with radio on) in this galaxy for range calculation."
				}
				// Use helper for object selection
				capturedPlanets := i.SelectObjectsWithCenters(
					conn,
					i.objects,
					centers,
					10,
					func(obj Object) bool {
						return obj.Galaxy == connInfo.Galaxy && obj.Type == "Planet" && obj.Side != "neutral"
					},
					false, // No radius filtering for captured planets
				)
				// Output
				if len(capturedPlanets) == 0 {
					return "Sir, there are no known captured planets in game"
				}
				// Sort by side, then by location
				sort.Slice(capturedPlanets, func(i, j int) bool {
					if capturedPlanets[i].Side != capturedPlanets[j].Side {
						return capturedPlanets[i].Side < capturedPlanets[j].Side
					}
					if capturedPlanets[i].LocationX != capturedPlanets[j].LocationX {
						return capturedPlanets[i].LocationX < capturedPlanets[j].LocationX
					}
					return capturedPlanets[i].LocationY < capturedPlanets[j].LocationY
				})
				var lines []string
				for _, obj := range capturedPlanets {
					rx := obj.LocationX - senderX
					ry := obj.LocationY - senderY
					nameOrType := obj.Type
					// Output abbreviation if short/medium
					if info, ok := i.connections.Load(conn); ok {
						connInfo := info.(ConnectionInfo)
						if connInfo.OutputState == "medium" || connInfo.OutputState == "short" {
							if obj.Side == senderSide {
								nameOrType = "+@"
							} else if obj.Side == "neutral" {
								nameOrType = "@"
							} else {
								nameOrType = "-@"
							}
						}
					}
					abbr := ""
					if info, ok := i.connections.Load(conn); ok {
						connInfo := info.(ConnectionInfo)
						if connInfo.OutputState == "medium" || connInfo.OutputState == "short" {
							abbr = ""
						} else {
							switch obj.Side {
							case "federation":
								abbr = "Fed"
							case "empire":
								abbr = "Emp"
							default:
								abbr = obj.Side
							}
						}
					}
					prefix := " "
					if obj.Side != senderSide {
						prefix = "*"
					}
					// Format coordinates based on ocdef setting
					var locationStr, rangeStr string
					if info, ok := i.connections.Load(conn); ok {
						connInfo := info.(ConnectionInfo)
						switch connInfo.OCdef {
						case "absolute":
							locationStr = fmt.Sprintf("@%d-%d", obj.LocationX, obj.LocationY)
							rangeStr = ""
						case "relative":
							locationStr = fmt.Sprintf("%+d,%+d", rx, ry)
							rangeStr = ""
						case "both":
							locationStr = fmt.Sprintf("@%d-%d", obj.LocationX, obj.LocationY)
							rangeStr = fmt.Sprintf("%+d,%+d", rx, ry)
						default:
							locationStr = fmt.Sprintf("%+d,%+d", rx, ry)
							rangeStr = ""
						}
					} else {
						locationStr = fmt.Sprintf("%+d,%+d", rx, ry)
						rangeStr = ""
					}

					shieldPct := float64(obj.Shields) / float64(InitialShieldValue) * 100.0
					shieldStr := fmt.Sprintf("%.0f%%", float64(shieldPct))
					shieldudflag := "-"
					if obj.ShieldsUpDown == true {
						shieldudflag = "+"
					}
					shieldStr = shieldudflag + shieldStr
					lines = append(lines, prefix+fmt.Sprintf("%-3s %-11s %-8s %-8s %s",
						abbr,
						nameOrType,
						locationStr,
						rangeStr,
						shieldStr))
				}
				return strings.Join(lines, "\r\n")
			}

			// Check for <radius> parameter as the last argument
			radius := 10 // default radius
			radiusSpecified := false
			if len(resolvedKeywords) > 0 {
				last := resolvedKeywords[len(resolvedKeywords)-1]
				if r, err := strconv.Atoi(last); err == nil {
					radius = r
					resolvedKeywords = resolvedKeywords[:len(resolvedKeywords)-1]
					radiusSpecified = true
				}
			}

			if radius < 0 || radius > 10 {
				return "Radius must be <= 10"
			}

			// Check for ship name filtering
			var shipNameFilter string
			var hasShipNameFilter bool

			// Get all ships in the current galaxy to check for name matches
			if info, ok := i.connections.Load(conn); ok {
				connInfo := info.(ConnectionInfo)
				ships := i.getObjectsByType(connInfo.Galaxy, "Ship")
				if ships != nil {
					for _, obj := range ships {
						shipName := strings.ToLower(obj.Name)
						for _, kw := range resolvedKeywords {
							kwLower := strings.ToLower(kw)
							// Check if keyword is a prefix of the ship name
							if strings.HasPrefix(shipName, kwLower) {
								shipNameFilter = obj.Name
								hasShipNameFilter = true
								break
							}
						}
						if hasShipNameFilter {
							break
						}
					}
				}
			}

			// If no ship name filter was found, check if any keyword is a prefix of "romulan"
			// and return an appropriate message instead of falling through to show everything
			if !hasShipNameFilter {
				for _, kw := range resolvedKeywords {
					kwLower := strings.ToLower(kw)
					if !validKeywords[kwLower] && strings.HasPrefix("romulan", kwLower) && len(kwLower) >= 2 {
						return "Sir, there are no Romulans in game"
					}
				}
			}

			// Check for location-based filtering (e.g., "7-35" or "7 35")
			var locationX, locationY int
			var hasLocationFilter bool

			// Skip location filtering if ship name filter is active
			if !hasShipNameFilter {
				for _, kw := range resolvedKeywords {
					// Check for "X-Y" format
					if strings.Contains(kw, "-") {
						parts := strings.Split(kw, "-")
						if len(parts) == 2 {
							if x, y, err := i.parseCoordinates(strings.TrimSpace(parts[0]), strings.TrimSpace(parts[1]), conn, false); err == nil {
								locationX, locationY = x, y
								hasLocationFilter = true
								break
							}
						}
					}
				}

				// Also check if we have two consecutive numeric keywords (e.g., "7" "35"), uses largest.
				if !hasLocationFilter {
					for idx := 0; idx < len(resolvedKeywords)-1; idx++ {
						if x, y, err := i.parseCoordinates(resolvedKeywords[idx], resolvedKeywords[idx+1], conn, false); err == nil {
							locationX, locationY = x, y
							hasLocationFilter = true
							break
						}
					}
				}
			}

			if len(i.objects) == 0 {
				return "No objects in the database"
			}

			// Check if summary is requested
			wantSummary := contains(resolvedKeywords, "summary")

			type objectEntry struct {
				obj          Object
				distance     float64
				isOutOfRange bool // Flag to indicate if object is out of range of any friendly center
			}
			var filtered []objectEntry

			if len(resolvedKeywords) > 0 && resolvedKeywords[0] == "closest" && !hasShipNameFilter {
				// --- closest subcommand: use ship and friendly ships with radio on as centers (consistent with regular list) ---
				var targetType string
				if len(resolvedKeywords) >= 2 && !hasLocationFilter {
					targetType = resolvedKeywords[1]
					if !validClosestTypes[targetType] {
						return fmt.Sprintf("Error: invalid type after 'closest': %s. Use base, enemy, friendly, neutral, planet, star, ship, or blackhole", targetType)
					}
				}
				if len(resolvedKeywords) > 2 && !hasLocationFilter {
					return "Error: too many parameters for 'closest'. Use 'closest' or 'closest <type>'"
				}

				// Build centers: player's ship + friendly ships with radio on (consistent with regular list)
				var closestCenters []struct{ X, Y int }
				closestCenters = append(closestCenters, struct{ X, Y int }{X: senderX, Y: senderY})
				for _, obj := range i.objects {
					if obj.Galaxy == connInfo.Galaxy && obj.Type == "Ship" && obj.Side == senderSide && obj.RadioOnOff && obj.Name != connInfo.Shipname {
						closestCenters = append(closestCenters, struct{ X, Y int }{X: obj.LocationX, Y: obj.LocationY})
					}
				}

				// Determine which object types to search based on targetType
				var typesToSearch []string
				if targetType == "" && !hasLocationFilter {
					// No type specified, search all types except stars and black holes
					typesToSearch = []string{"Ship", "Base", "Planet"}
				} else {
					switch targetType {
					case "base":
						typesToSearch = []string{"Base"}
					case "planet":
						typesToSearch = []string{"Planet"}
					case "star":
						typesToSearch = []string{"Star"}
					case "ship":
						typesToSearch = []string{"Ship"}
					case "blackhole":
						typesToSearch = []string{"Black Hole"}
					case "ports":
						typesToSearch = []string{"Base", "Planet"}
					case "enemy", "friendly", "neutral", "human", "empire", "targets", "captured":
						// These filter by side, so we need to check all object types
						typesToSearch = []string{"Ship", "Base", "Planet"}
					default:
						if hasLocationFilter {
							// Location filter, search all types
							typesToSearch = []string{"Ship", "Base", "Planet", "Star", "Black Hole"}
						} else {
							typesToSearch = []string{"Ship", "Base", "Planet"}
						}
					}
				}

				// Search through specific object types using objectsByType
				for _, objType := range typesToSearch {
					objects := i.getObjectsByType(connInfo.Galaxy, objType)
					if objects == nil {
						continue
					}

					for _, obj := range objects {
						if connInfo.Ship != nil && obj.Type == "Ship" && obj.Name == connInfo.Ship.Name {
							continue // Skip the player's own ship
						}
						if obj.Type == "Star" && targetType != "star" && !hasLocationFilter {
							continue // Skip stars unless specifically requested or location filter
						}
						if obj.Type == "Black Hole" && targetType != "blackhole" && !hasLocationFilter {
							continue // Skip black holes unless specifically requested or location filter
						}

						// Apply location filter if specified
						if hasLocationFilter {
							if obj.LocationX != locationX || obj.LocationY != locationY {
								continue
							}
						}

						matches := false
						if targetType == "" && !hasLocationFilter {
							matches = true // No type specified, match all
						} else if hasLocationFilter {
							matches = true // Location filter already applied above
						} else {
							switch targetType {
							case "base":
								matches = (strings.ToLower(obj.Type) == "base")
							case "planet":
								matches = (strings.ToLower(obj.Type) == "planet")
							case "star":
								matches = (strings.ToLower(obj.Type) == "star")
							case "ship":
								matches = (strings.ToLower(obj.Type) == "ship")
							case "enemy":
								matches = (obj.Side != senderSide && obj.Side != "neutral")
							case "friendly":
								matches = (obj.Side == senderSide)
							case "neutral":
								matches = (obj.Side == "neutral")
							case "blackhole":
								matches = (strings.ToLower(obj.Type) == "black hole")
							case "ports":
								// Ports = bases and planets, default to friendly if no side specified
								isPort := (strings.ToLower(obj.Type) == "base" || strings.ToLower(obj.Type) == "planet")
								if !isPort {
									matches = false
								} else {
									// Check if any side keyword was specified
									hasSideKeyword := contains(resolvedKeywords, "friendly") || contains(resolvedKeywords, "enemy") || contains(resolvedKeywords, "neutral") || contains(resolvedKeywords, "human") || contains(resolvedKeywords, "empire") || contains(resolvedKeywords, "federation") || contains(resolvedKeywords, "targets") || contains(resolvedKeywords, "captured")
									if !hasSideKeyword {
										// Default to friendly ports
										matches = (obj.Side == senderSide)
									} else {
										// Side will be handled by regular filtering
										matches = true
									}
								}
							case "human":
								matches = (obj.Side == "federation" || obj.Side == "empire") && obj.Type == "Ship"
							case "empire":
								matches = (obj.Side == "empire")
							case "federation":
								matches = (obj.Side == "federation")
							case "targets":
								matches = (obj.Side != senderSide && obj.Side != "neutral")
							case "captured":
								matches = (obj.Side != senderSide && obj.Side != "neutral") && obj.Type == "Planet"
							}
						}

						if !matches {
							continue
						}

						// Check if the object is within box radius of ANY center (consistent with SelectObjectsWithCenters)
						inRange := false
						if hasLocationFilter {
							inRange = true
						} else {
							for _, center := range closestCenters {
								dx := obj.LocationX - center.X
								dy := obj.LocationY - center.Y
								if dx < 0 {
									dx = -dx
								}
								if dy < 0 {
									dy = -dy
								}
								if dx <= radius && dy <= radius {
									inRange = true
									break
								}
							}
						}

						if inRange {
							distance := math.Sqrt(math.Pow(float64(obj.LocationX-senderX), 2) + math.Pow(float64(obj.LocationY-senderY), 2))
							filtered = append(filtered, objectEntry{obj: *obj, distance: distance})
						}
					}
				}

				if len(filtered) == 0 {
					if hasLocationFilter {
						return fmt.Sprintf("No objects found at location %d-%d in galaxy %d", locationX, locationY, connInfo.Galaxy)
					}
					typeStr := "matching"
					if targetType != "" {
						typeStr = targetType
					}
					return fmt.Sprintf("No %s objects found within 10 sectors in galaxy %d", typeStr, connInfo.Galaxy)
				}

				sort.Slice(filtered, func(i, j int) bool {
					return filtered[i].distance < filtered[j].distance
				})
				filtered = filtered[:1] // Take the closest one

				// Generate the output for the closest object
				var lines []string
				for _, entry := range filtered {
					obj := entry.obj
					rx := obj.LocationX - senderX
					ry := obj.LocationY - senderY

					nameOrType := obj.Name
					if obj.Type != "Ship" {
						nameOrType = obj.Type
						// Check output state for object abbreviations
						if info, ok := i.connections.Load(conn); ok {
							connInfo := info.(ConnectionInfo)
							if connInfo.OutputState == "medium" || connInfo.OutputState == "short" {
								switch obj.Type {
								case "Planet":
									if obj.Side == senderSide {
										nameOrType = "+@"
									} else if obj.Side == "neutral" {
										nameOrType = "@"
									} else {
										nameOrType = "-@"
									}
								case "Base":
									if obj.Side == "federation" {
										nameOrType = "[]"
									} else if obj.Side == "empire" {
										nameOrType = "()"
									}
									// Other base types (neutral, romulan) keep "Base"
								case "Star":
									nameOrType = "*"
								case "Black Hole":
									nameOrType = "BH"
								}
							}
						}
					} else {
						// Check output state for ship name abbreviation
						if info, ok := i.connections.Load(conn); ok {
							connInfo := info.(ConnectionInfo)
							if connInfo.OutputState == "medium" || connInfo.OutputState == "short" {
								if len(obj.Name) > 0 {
									if obj.Side == "romulan" {
										nameOrType = "~~"
									} else {
										nameOrType = string(obj.Name[0])
									}
								}
							}
						}
					}

					prefix := " "
					if obj.Side != senderSide && obj.Side != "neutral" {
						prefix = "*"
					}

					// Print abbreviated side
					abbr := ""
					if info, ok := i.connections.Load(conn); ok {
						connInfo := info.(ConnectionInfo)
						if connInfo.OutputState == "medium" || connInfo.OutputState == "short" {
							abbr = ""
						} else {
							switch obj.Side {
							case "federation":
								abbr = "Fed"
							case "empire":
								abbr = "Emp"
							case "neutral":
								abbr = "Neu"
							case "romulan":
								abbr = "Rom"
							default:
								abbr = obj.Side
							}
						}
					} else {
						switch obj.Side {
						case "federation":
							abbr = "Fed"
						case "empire":
							abbr = "Emp"
						case "neutral":
							abbr = "Neu"
						case "romulan":
							abbr = "Rom"
						default:
							abbr = obj.Side
						}
					}
					// Format coordinates based on ocdef setting
					var locationStr, rangeStr string
					if info, ok := i.connections.Load(conn); ok {
						connInfo := info.(ConnectionInfo)
						switch connInfo.OCdef {
						case "absolute":
							locationStr = fmt.Sprintf("@%d-%d", obj.LocationX, obj.LocationY)
							rangeStr = ""
						case "relative":
							locationStr = fmt.Sprintf("%+d,%+d", rx, ry)
							rangeStr = ""
						case "both":
							locationStr = fmt.Sprintf("@%d-%d", obj.LocationX, obj.LocationY)
							rangeStr = fmt.Sprintf("%+d,%+d", rx, ry)
						default: // Default to relative
							locationStr = fmt.Sprintf("%+d,%+d", rx, ry)
							rangeStr = ""
						}
					} else {
						locationStr = fmt.Sprintf("%+d,%+d", rx, ry)
						rangeStr = ""
					}

					shieldPct := float64(obj.Shields) / float64(InitialShieldValue) * 100.0
					shieldStr := fmt.Sprintf("%.0f%%", float64(shieldPct))
					shieldudflag := "-"
					if obj.ShieldsUpDown == true {
						shieldudflag = "+"
					}
					shieldStr = shieldudflag + shieldStr

					lines = append(lines, prefix+fmt.Sprintf("%-3s %-11s %-8s %-8s %s",
						abbr,
						nameOrType,
						locationStr,
						rangeStr,
						shieldStr))
				}

				// Return results
				return strings.Join(lines, "\r\n")
			} else if hasShipNameFilter {
				// --- ship name filtering: show only the specified ship ---
				for _, obj := range i.objects {
					if obj.Galaxy != connInfo.Galaxy {
						continue
					}
					if obj.Type != "Ship" || obj.Name != shipNameFilter {
						continue
					}

					rx := obj.LocationX - senderX
					ry := obj.LocationY - senderY

					nameOrType := obj.Name
					// Check output state for ship name abbreviation
					if info, ok := i.connections.Load(conn); ok {
						connInfo := info.(ConnectionInfo)
						if connInfo.OutputState == "medium" || connInfo.OutputState == "short" {
							if len(obj.Name) > 0 {
								if obj.Side == "romulan" && connInfo.OutputState == "short" {
									nameOrType = "~~"
								} else {
									nameOrType = string(obj.Name[0])
								}
							}
						}
					}

					prefix := " "
					if obj.Side != senderSide && obj.Side != "neutral" {
						prefix = "*"
					}

					// Print abbreviated side
					abbr := ""
					if info, ok := i.connections.Load(conn); ok {
						connInfo := info.(ConnectionInfo)
						if connInfo.OutputState == "medium" || connInfo.OutputState == "short" {
							abbr = ""
						} else {
							switch obj.Side {
							case "federation":
								abbr = "Fed"
							case "empire":
								abbr = "Emp"
							case "neutral":
								abbr = "Neu"
							case "romulan":
								abbr = "Rom"
							default:
								abbr = obj.Side
							}
						}
					} else {
						switch obj.Side {
						case "federation":
							abbr = "Fed"
						case "empire":
							abbr = "Emp"
						case "neutral":
							abbr = "Neu"
						case "romulan":
							abbr = "Rom"
						default:
							abbr = obj.Side
						}
					}

					// Format coordinates based on ocdef setting
					var locationStr, rangeStr string
					if info, ok := i.connections.Load(conn); ok {
						connInfo := info.(ConnectionInfo)
						switch connInfo.OCdef {
						case "absolute":
							locationStr = fmt.Sprintf("@%d-%d", obj.LocationX, obj.LocationY)
							rangeStr = ""
						case "relative":
							locationStr = fmt.Sprintf("%+d,%+d", rx, ry)
							rangeStr = ""
						case "both":
							locationStr = fmt.Sprintf("@%d-%d", obj.LocationX, obj.LocationY)
							rangeStr = fmt.Sprintf("%+d,%+d", rx, ry)
						default: // Default to relative
							locationStr = fmt.Sprintf("%+d,%+d", rx, ry)
							rangeStr = ""
						}
					} else {
						locationStr = fmt.Sprintf("%+d,%+d", rx, ry)
						rangeStr = ""
					}

					var lines []string
					shieldPct := float64(obj.Shields) / float64(InitialShieldValue) * 100.0
					shieldStr := fmt.Sprintf("%.0f%%", float64(shieldPct))
					shieldudflag := "-"
					if obj.ShieldsUpDown == true {
						shieldudflag = "+"
					}
					shieldStr = shieldudflag + shieldStr

					lines = append(lines, prefix+fmt.Sprintf("%-3s %-11s %-8s %-8s %s",
						abbr,
						nameOrType,
						locationStr,
						rangeStr,
						shieldStr))

					return strings.Join(lines, "\r\n")
				}

				// Ship not found
				return fmt.Sprintf("Ship '%s' not found in galaxy %d", shipNameFilter, connInfo.Galaxy)
			} else {
				// --- all other subcommands: use your ship and all other ships on your side with radio up as centers ---
				var centers []struct{ X, Y int }
				centers = append(centers, struct{ X, Y int }{X: senderX, Y: senderY})
				for _, obj := range i.objects {
					if obj.Galaxy == connInfo.Galaxy && obj.Type == "Ship" && obj.Side == senderSide && obj.RadioOnOff && obj.Name != connInfo.Shipname {
						centers = append(centers, struct{ X, Y int }{X: obj.LocationX, Y: obj.LocationY})
					}
				}

				if len(centers) == 0 {
					return "No valid centers (your ship or friendly ships with radio on) in this galaxy for range calculation."
				}

				// Use SelectObjectsWithCenters for main selection logic
				selectedObjects := i.SelectObjectsWithCenters(
					conn,
					i.objects,
					centers,
					radius,
					func(obj Object) bool {
						if obj.Galaxy != connInfo.Galaxy {
							return false
						}
						if obj.Type == "Star" {
							return false
						}
						if obj.Type == "Black Hole" {
							return false
						}
						// Apply location filter if specified
						if hasLocationFilter && (obj.LocationX != locationX || obj.LocationY != locationY) {
							return false
						}
						// Apply ship name filter if specified
						if hasShipNameFilter && (obj.Type != "Ship" || obj.Name != shipNameFilter) {
							return false
						}
						// Apply keyword filtering
						sideMatch := false
						typeMatch := false
						isPortsQuery := contains(resolvedKeywords, "ports")
						for _, kw := range resolvedKeywords {
							switch kw {
							case "neutral":
								if obj.Side == "neutral" {
									sideMatch = true
								}
							case "friendly":
								if obj.Side == senderSide {
									sideMatch = true
								}
							case "enemy":
								if obj.Side != senderSide && obj.Side != "neutral" {
									sideMatch = true
								}
							case "human":
								if (obj.Side == "federation" || obj.Side == "empire") && obj.Type == "Ship" {
									sideMatch = true
								}
							case "empire":
								if obj.Side == "empire" {
									sideMatch = true
								}
							case "federation":
								if obj.Side == "federation" {
									sideMatch = true
								}
							case "targets":
								if obj.Side != senderSide && obj.Side != "neutral" {
									sideMatch = true
								}
							case "captured":
								if (obj.Side != senderSide && obj.Side != "neutral") && obj.Type == "Planet" {
									sideMatch = true
								}
							case "ships":
								if obj.Type == "Ship" {
									typeMatch = true
								}
							case "bases":
								if obj.Type == "Base" {
									typeMatch = true
								}
							case "planets":
								if obj.Type == "Planet" {
									typeMatch = true
								}
							case "blackholes":
								if obj.Type == "Black Hole" {
									typeMatch = true
								}
							case "ports":
								if obj.Type == "Base" || obj.Type == "Planet" {
									typeMatch = true
								}
							}
						}
						if (contains(resolvedKeywords, "neutral") || contains(resolvedKeywords, "friendly") || contains(resolvedKeywords, "enemy") || contains(resolvedKeywords, "human") || contains(resolvedKeywords, "empire") || contains(resolvedKeywords, "federation") || contains(resolvedKeywords, "targets") || contains(resolvedKeywords, "captured")) && !sideMatch {
							return false
						}
						if (contains(resolvedKeywords, "ships") || contains(resolvedKeywords, "bases") || contains(resolvedKeywords, "planets") || contains(resolvedKeywords, "blackholes") || contains(resolvedKeywords, "ports")) && !typeMatch {
							return false
						}
						if isPortsQuery && !contains(resolvedKeywords, "neutral") && !contains(resolvedKeywords, "friendly") && !contains(resolvedKeywords, "enemy") && !contains(resolvedKeywords, "human") && !contains(resolvedKeywords, "empire") && !contains(resolvedKeywords, "federation") && !contains(resolvedKeywords, "targets") && !contains(resolvedKeywords, "captured") {
							if obj.Side != senderSide {
								return false
							}
						}
						return true
					},
					radiusSpecified, // Pass the flag here
				)

				// Using a map to ensure unique objects are added, similar to original logic,
				// but now storing objectEntry with isOutOfRange flag
				objectMap := make(map[string]objectEntry)
				for _, obj := range selectedObjects {
					// Determine if the object is in range of any center
					isInRange := false
					minDistance := math.Inf(1)
					for _, center := range centers {
						dx := obj.LocationX - center.X
						dy := obj.LocationY - center.Y
						absDx := AbsInt(dx)
						absDy := AbsInt(dy)
						manhattan := float64(absDx + absDy)
						if manhattan < minDistance {
							minDistance = manhattan
						}
						if absDx <= radius && absDy <= radius {
							isInRange = true
						}
					}
					// Special case: Player's own ship is always listed and never out of range.
					if connInfo.Ship != nil && obj.Type == "Ship" && obj.Name == connInfo.Ship.Name {
						key := fmt.Sprintf("%s-%d-%d-%s-%d", obj.Type, obj.LocationX, obj.LocationY, obj.Side, obj.Galaxy)
						objectMap[key] = objectEntry{obj: *obj, distance: minDistance, isOutOfRange: false}
						continue
					}
					if obj.Type == "Ship" {
						outOfRangeFlag := !isInRange
						key := fmt.Sprintf("%s-%d-%d-%s-%d", obj.Type, obj.LocationX, obj.LocationY, obj.Side, obj.Galaxy)
						objectMap[key] = objectEntry{obj: *obj, distance: minDistance, isOutOfRange: outOfRangeFlag}
					} else {
						if DecwarMode == true {
							// For non-ship objects, they are always considered "in range" for listing purposes
							// because their presence in selectedObjects means they have been seen before.
							key := fmt.Sprintf("%s-%d-%d-%s-%d", obj.Type, obj.LocationX, obj.LocationY, obj.Side, obj.Galaxy)
							objectMap[key] = objectEntry{obj: *obj, distance: minDistance, isOutOfRange: false}
						} else {
							if isInRange {
								key := fmt.Sprintf("%s-%d-%d-%s-%d", obj.Type, obj.LocationX, obj.LocationY, obj.Side, obj.Galaxy)
								objectMap[key] = objectEntry{obj: *obj, distance: minDistance, isOutOfRange: false}
							}

						}
					}
				}
				for _, entry := range objectMap {
					filtered = append(filtered, entry)
				}

				// Sort: Ships first, then by type, then X, then Y
				sort.Slice(filtered, func(i, j int) bool {
					isShipI := filtered[i].obj.Type == "Ship"
					isShipJ := filtered[j].obj.Type == "Ship"

					if isShipI != isShipJ {
						return isShipI // True if i is a ship and j is not, so ships come first
					}

					// If both are ships or both are non-ships, sort by type, then location
					if filtered[i].obj.Type != filtered[j].obj.Type {
						return filtered[i].obj.Type < filtered[j].obj.Type
					}
					if filtered[i].obj.LocationX != filtered[j].obj.LocationX {
						return filtered[i].obj.LocationX < filtered[j].obj.LocationX
					}
					return filtered[i].obj.LocationY < filtered[j].obj.LocationY
				})
			}

			var lines []string

			// Split filtered into ships and non-ships
			var ships, nonShips []objectEntry
			for _, entry := range filtered {
				if entry.obj.Type == "Ship" {
					ships = append(ships, entry)
				} else {
					nonShips = append(nonShips, entry)
				}
			}

			// Pre-compute summary data if needed
			// Only print " in game" suffix for long or medium output
			inGameSuffix := ""
			if connInfo.OutputState == "long" || connInfo.OutputState == "medium" {
				inGameSuffix = " in game"
			}
			// sideSortPriority defines the display ordering: federation first, then empire, neutral, romulan
			sideSortPriority := func(side string) int {
				switch side {
				case "federation":
					return 0
				case "empire":
					return 1
				case "neutral":
					return 2
				case "romulan":
					return 3
				default:
					return 4
				}
			}

			// Sort ships by side (federation before empire), then by name
			sort.Slice(ships, func(i, j int) bool {
				pi, pj := sideSortPriority(ships[i].obj.Side), sideSortPriority(ships[j].obj.Side)
				if pi != pj {
					return pi < pj
				}
				return ships[i].obj.Name < ships[j].obj.Name
			})

			// Sort non-ships by type first, then by side, then by location
			sort.Slice(nonShips, func(i, j int) bool {
				if nonShips[i].obj.Type != nonShips[j].obj.Type {
					return nonShips[i].obj.Type < nonShips[j].obj.Type
				}
				pi, pj := sideSortPriority(nonShips[i].obj.Side), sideSortPriority(nonShips[j].obj.Side)
				if pi != pj {
					return pi < pj
				}
				if nonShips[i].obj.LocationX != nonShips[j].obj.LocationX {
					return nonShips[i].obj.LocationX < nonShips[j].obj.LocationX
				}
				return nonShips[i].obj.LocationY < nonShips[j].obj.LocationY
			})

			// Helper to generate a summary line for a specific (type, side) group
			generateGroupSummaryLine := func(objType string, side string, count int) string {
				var typeName string
				if count == 1 {
					switch objType {
					case "Base":
						typeName = "base"
					case "Ship":
						typeName = "ship"
					case "Planet":
						typeName = "planet"
					case "Black Hole":
						typeName = "black hole"
					case "Star":
						typeName = "star"
					default:
						typeName = objType
					}
				} else {
					switch objType {
					case "Base":
						typeName = "bases"
					case "Ship":
						typeName = "ships"
					case "Planet":
						typeName = "planets"
					case "Black Hole":
						typeName = "black holes"
					case "Star":
						typeName = "stars"
					default:
						typeName = objType
					}
				}
				sideNames := map[string]string{
					"federation": "Federation",
					"empire":     "Empire",
					"neutral":    "neutral",
					"romulan":    "Romulan",
				}
				sideName := sideNames[side]
				if sideName == "" {
					sideName = side
				}
				return fmt.Sprintf("%3d %s %s%s", count, sideName, typeName, inGameSuffix)
			}

			// Helper to check if an object matches the keyword type/side filters
			// (same logic as the SelectObjectsWithCenters filter, but without galaxy/range checks)
			matchesKeywordFilter := func(obj Object) bool {
				if obj.Type == "Star" {
					return false
				}
				if obj.Type == "Black Hole" {
					return false
				}
				// Apply keyword filtering
				sideMatch := false
				typeMatch := false
				isPortsQuery := contains(resolvedKeywords, "ports")
				for _, kw := range resolvedKeywords {
					switch kw {
					case "neutral":
						if obj.Side == "neutral" {
							sideMatch = true
						}
					case "friendly":
						if obj.Side == senderSide {
							sideMatch = true
						}
					case "enemy":
						if obj.Side != senderSide && obj.Side != "neutral" {
							sideMatch = true
						}
					case "human":
						if (obj.Side == "federation" || obj.Side == "empire") && obj.Type == "Ship" {
							sideMatch = true
						}
					case "empire":
						if obj.Side == "empire" {
							sideMatch = true
						}
					case "targets":
						if obj.Side != senderSide && obj.Side != "neutral" {
							sideMatch = true
						}
					case "captured":
						if (obj.Side != senderSide && obj.Side != "neutral") && obj.Type == "Planet" {
							sideMatch = true
						}
					case "ships":
						if obj.Type == "Ship" {
							typeMatch = true
						}
					case "bases":
						if obj.Type == "Base" {
							typeMatch = true
						}
					case "planets":
						if obj.Type == "Planet" {
							typeMatch = true
						}
					case "blackholes":
						if obj.Type == "Black Hole" {
							typeMatch = true
						}
					case "ports":
						if obj.Type == "Base" || obj.Type == "Planet" {
							typeMatch = true
						}
					}
				}
				if (contains(resolvedKeywords, "neutral") || contains(resolvedKeywords, "friendly") || contains(resolvedKeywords, "enemy") || contains(resolvedKeywords, "human") || contains(resolvedKeywords, "empire") || contains(resolvedKeywords, "targets") || contains(resolvedKeywords, "captured")) && !sideMatch {
					return false
				}
				if (contains(resolvedKeywords, "ships") || contains(resolvedKeywords, "bases") || contains(resolvedKeywords, "planets") || contains(resolvedKeywords, "blackholes") || contains(resolvedKeywords, "ports")) && !typeMatch {
					return false
				}
				if isPortsQuery && !contains(resolvedKeywords, "neutral") && !contains(resolvedKeywords, "friendly") && !contains(resolvedKeywords, "enemy") && !contains(resolvedKeywords, "human") && !contains(resolvedKeywords, "empire") && !contains(resolvedKeywords, "targets") && !contains(resolvedKeywords, "captured") {
					if obj.Side != senderSide {
						return false
					}
				}
				return true
			}

			// Print ships first (no blank lines between side groups)
			for _, entry := range ships {
				obj := entry.obj
				rx := obj.LocationX - senderX
				ry := obj.LocationY - senderY

				nameOrType := obj.Name
				// Check output state for ship name abbreviation
				if info, ok := i.connections.Load(conn); ok {
					connInfo := info.(ConnectionInfo)
					if connInfo.OutputState == "medium" || connInfo.OutputState == "short" {
						if len(obj.Name) > 0 {
							if obj.Side == "romulan" && connInfo.OutputState == "short" {
								nameOrType = "~~"
							} else {
								nameOrType = string(obj.Name[0])
							}
						}
					}
				}

				prefix := " "
				if obj.Side != senderSide && obj.Side != "neutral" {
					prefix = "*"
				}

				// Format coordinates based on ocdef setting
				var locationStr, rangeStr string
				if entry.isOutOfRange {
					locationStr = "out of range"
					rangeStr = ""
				} else {
					if info, ok := i.connections.Load(conn); ok {
						connInfo := info.(ConnectionInfo)
						switch connInfo.OCdef {
						case "absolute":
							locationStr = fmt.Sprintf("@%d-%d", obj.LocationX, obj.LocationY)
							rangeStr = ""
						case "relative":
							locationStr = fmt.Sprintf("%+d,%+d", rx, ry)
							rangeStr = ""
						case "both":
							locationStr = fmt.Sprintf("@%d-%d", obj.LocationX, obj.LocationY)
							rangeStr = fmt.Sprintf("%+d,%+d", rx, ry)
						default: // Default to relative
							locationStr = fmt.Sprintf("%+d,%+d", rx, ry)
							rangeStr = ""
						}
					} else {
						locationStr = fmt.Sprintf("%+d,%+d", rx, ry)
						rangeStr = ""
					}
				}

				shieldPct := float64(obj.Shields) / float64(InitialShieldValue) * 100.0
				shieldStr := fmt.Sprintf("%.0f%%", float64(shieldPct))
				shieldudflag := "-"
				if obj.ShieldsUpDown == true {
					shieldudflag = "+"
				}
				shieldStr = shieldudflag + shieldStr

				if entry.isOutOfRange || obj.Side == "neutral" {
					shieldStr = "" // Don't print shield strength if out of range or neutral
				}

				// Print abbreviated side for ships
				abbr := ""
				if info, ok := i.connections.Load(conn); ok {
					connInfo := info.(ConnectionInfo)
					if connInfo.OutputState == "medium" || connInfo.OutputState == "short" {
						abbr = ""
					} else {
						switch obj.Side {
						case "federation":
							abbr = "Fed"
						case "empire":
							abbr = "Emp"
						case "neutral":
							abbr = "Neu"
						case "romulan":
							abbr = "Rom"
						default:
							abbr = obj.Side
						}
					}
				} else {
					switch obj.Side {
					case "federation":
						abbr = "Fed"
					case "empire":
						abbr = "Emp"
					case "neutral":
						abbr = "Neu"
					case "romulan":
						abbr = "Rom"
					default:
						abbr = obj.Side
					}
				}
				lines = append(lines, prefix+fmt.Sprintf("%-3s %-11s %-8s %-8s %s",
					abbr,
					nameOrType,
					locationStr,
					rangeStr,
					shieldStr))
			}

			// Then print non-ships (no blank lines between side groups)
			for _, entry := range nonShips {
				obj := entry.obj
				rx := obj.LocationX - senderX
				ry := obj.LocationY - senderY

				nameOrType := obj.Type
				// Check output state for object abbreviations
				if info, ok := i.connections.Load(conn); ok {
					connInfo := info.(ConnectionInfo)
					if connInfo.OutputState == "medium" || connInfo.OutputState == "short" {
						switch obj.Type {
						case "Planet":
							if obj.Side == senderSide {
								nameOrType = "+@"
							} else if obj.Side == "neutral" {
								nameOrType = "@"
							} else {
								nameOrType = "-@"
							}
						case "Base":
							if obj.Side == "federation" {
								nameOrType = "[]"
							} else if obj.Side == "empire" {
								nameOrType = "()"
							}
							// Other base types (neutral, romulan) keep "Base"
						case "Star":
							nameOrType = "*"
						case "Black Hole":
							nameOrType = "BH"
						}
					}
				}

				prefix := " "
				if obj.Side != senderSide && obj.Side != "neutral" {
					prefix = "*"
				}

				// Print abbreviated side for non-ships
				abbr := ""
				if info, ok := i.connections.Load(conn); ok {
					connInfo := info.(ConnectionInfo)
					if connInfo.OutputState == "medium" || connInfo.OutputState == "short" {
						abbr = ""
					} else {
						switch obj.Side {
						case "federation":
							abbr = "Fed"
						case "empire":
							abbr = "Emp"
						case "neutral":
							abbr = "Neu"
						case "romulan":
							abbr = "Rom"
						default:
							abbr = obj.Side
						}
					}
				} else {
					switch obj.Side {
					case "federation":
						abbr = "Fed"
					case "empire":
						abbr = "Emp"
					case "neutral":
						abbr = "Neu"
					case "romulan":
						abbr = "Rom"
					default:
						abbr = obj.Side
					}
				}
				// Format coordinates based on ocdef setting
				var locationStr, rangeStr string
				if info, ok := i.connections.Load(conn); ok {
					connInfo := info.(ConnectionInfo)
					switch connInfo.OCdef {
					case "absolute":
						locationStr = fmt.Sprintf("@%d-%d", obj.LocationX, obj.LocationY)
						rangeStr = ""
					case "relative":
						locationStr = fmt.Sprintf("%+d,%+d", rx, ry)
						rangeStr = ""
					case "both":
						locationStr = fmt.Sprintf("@%d-%d", obj.LocationX, obj.LocationY)
						rangeStr = fmt.Sprintf("%+d,%+d", rx, ry)
					default: // Default to relative
						locationStr = fmt.Sprintf("%+d,%+d", rx, ry)
						rangeStr = ""
					}
				} else {
					locationStr = fmt.Sprintf("%+d,%+d", rx, ry)
					rangeStr = ""
				}

				shieldPct := float64(obj.Shields) / float64(InitialShieldValue) * 100.0
				shieldStr := fmt.Sprintf("%.0f%%", float64(shieldPct))
				shieldudflag := "-"
				if obj.ShieldsUpDown == true {
					shieldudflag = "+"
				}
				shieldStr = shieldudflag + shieldStr

				if obj.Side == "neutral" {
					shieldStr = ""
				}
				lines = append(lines, prefix+fmt.Sprintf("%-3s %-11s %-8s %-8s %s",
					abbr,
					nameOrType,
					locationStr,
					rangeStr,
					shieldStr))

			}

			// Append summary lines at the end using grand totals from the entire galaxy
			if wantSummary && len(filtered) > 0 {
				// Add a blank line before summary
				lines = append(lines, "")

				// Count grand totals for all objects in the galaxy matching keyword filters
				type typeSideKey struct {
					Type string
					Side string
				}
				grandTotals := make(map[typeSideKey]int)
				for _, obj := range i.objects {
					if obj.Galaxy != connInfo.Galaxy {
						continue
					}
					if !matchesKeywordFilter(*obj) {
						continue
					}
					key := typeSideKey{Type: obj.Type, Side: obj.Side}
					grandTotals[key]++
				}

				// Determine display order: Ships first, then Bases, then Planets, then others
				// Within each type, order by side priority
				typePriority := map[string]int{
					"Ship":       0,
					"Base":       1,
					"Planet":     2,
					"Black Hole": 3,
					"Star":       4,
				}
				sideOrder := []string{"federation", "empire", "neutral", "romulan"}

				// Collect keys and sort them
				var sortedKeys []typeSideKey
				for key := range grandTotals {
					sortedKeys = append(sortedKeys, key)
				}
				sort.Slice(sortedKeys, func(a, b int) bool {
					tp1, ok1 := typePriority[sortedKeys[a].Type]
					if !ok1 {
						tp1 = 99
					}
					tp2, ok2 := typePriority[sortedKeys[b].Type]
					if !ok2 {
						tp2 = 99
					}
					if tp1 != tp2 {
						return tp1 < tp2
					}
					return sideSortPriority(sortedKeys[a].Side) < sideSortPriority(sortedKeys[b].Side)
				})

				// Check for human keyword special case
				if contains(resolvedKeywords, "human") {
					humanTotal := 0
					for key, count := range grandTotals {
						if key.Type == "Ship" && (key.Side == "federation" || key.Side == "empire") {
							humanTotal += count
						}
					}
					if humanTotal > 0 {
						suffix := "ships"
						if humanTotal == 1 {
							suffix = "ship"
						}
						lines = append(lines, fmt.Sprintf("%3d Human %s%s", humanTotal, suffix, inGameSuffix))
					}
				}

				// Print per-(type, side) summary lines
				for _, key := range sortedKeys {
					count := grandTotals[key]
					if count <= 0 {
						continue
					}
					// Skip individual ship sides if "human" keyword is active (already printed combined)
					if contains(resolvedKeywords, "human") && key.Type == "Ship" && (key.Side == "federation" || key.Side == "empire") {
						continue
					}
					lines = append(lines, generateGroupSummaryLine(key.Type, key.Side, count))
				}

				// For captured keyword, add captured total
				if contains(resolvedKeywords, "captured") {
					capturedCount := 0
					for _, obj := range i.objects {
						if obj.Galaxy != connInfo.Galaxy {
							continue
						}
						if (obj.Side != senderSide && obj.Side != "neutral") && obj.Type == "Planet" {
							capturedCount++
						}
					}
					if capturedCount > 0 {
						suffix := "planets"
						if capturedCount == 1 {
							suffix = "planet"
						}
						lines = append(lines, fmt.Sprintf("%3d Captured %s%s", capturedCount, suffix, inGameSuffix))
					}
				}

				// Cross-type summaries (ports, klingon, targets)
				var crossTypeSummary []string

				// For ports summary (bases + planets combined)
				if contains(resolvedKeywords, "ports") {
					portsCounts := make(map[string]int)
					for _, obj := range i.objects {
						if obj.Galaxy != connInfo.Galaxy {
							continue
						}
						if obj.Type == "Base" || obj.Type == "Planet" {
							if matchesKeywordFilter(*obj) {
								portsCounts[obj.Side]++
							}
						}
					}
					sideNames := map[string]string{"federation": "Federation", "empire": "Empire", "neutral": "neutral", "romulan": "Romulan"}
					for _, side := range sideOrder {
						if count, ok := portsCounts[side]; ok && count > 0 {
							crossTypeSummary = append(crossTypeSummary, fmt.Sprintf("%3d %s Ports%s", count, sideNames[side], inGameSuffix))
						}
					}
				}

				// For empire summary (Empire objects across all types)
				if contains(resolvedKeywords, "empire") {
					empireCount := 0
					for _, obj := range i.objects {
						if obj.Galaxy != connInfo.Galaxy {
							continue
						}
						if obj.Side == "empire" && matchesKeywordFilter(*obj) {
							empireCount++
						}
					}
					if empireCount > 0 {
						suffix := "objects"
						if empireCount == 1 {
							suffix = "object"
						}
						crossTypeSummary = append(crossTypeSummary, fmt.Sprintf("%3d Empire %s%s", empireCount, suffix, inGameSuffix))
					}
				}

				// For targets summary (Enemy objects across all types)
				if contains(resolvedKeywords, "targets") {
					targetCount := 0
					for _, obj := range i.objects {
						if obj.Galaxy != connInfo.Galaxy {
							continue
						}
						if obj.Side != senderSide && obj.Side != "neutral" && matchesKeywordFilter(*obj) {
							targetCount++
						}
					}
					if targetCount > 0 {
						suffix := "targets"
						if targetCount == 1 {
							suffix = "target"
						}
						crossTypeSummary = append(crossTypeSummary, fmt.Sprintf("%3d Enemy %s%s", targetCount, suffix, inGameSuffix))
					}
				}

				if len(crossTypeSummary) > 0 {
					lines = append(lines, crossTypeSummary...)
				}
			}

			i.trackerMutex.Lock()
			if tracker, exists := i.galaxyTracker[connInfo.Galaxy]; exists {
				tracker.LastActive = time.Now()
				i.galaxyTracker[connInfo.Galaxy] = tracker
			} else {
				now := time.Now()
				i.galaxyTracker[connInfo.Galaxy] = GalaxyTracker{GalaxyStart: now, LastActive: now}
			}
			i.trackerMutex.Unlock()

			return strings.Join(lines, "\r\n")
		},
		Help: "LIST ship, base, and planet info\r\n" +
			"Syntax: List [<keywords>]\r\n" +
			"\r\n" +
			"The following information is available via the LIST command:\r\n" +
			"- Name of any ship currently in the game (including the Romulan).\r\n" +
			"- Location and shield percent of any friendly ship, or any ship within\r\n" +
			"  scan range (10 sectors).\r\n" +
			"- Location and shield percent of any friendly base, or any base within\r\n" +
			"  range.\r\n" +
			"- Location of any known enemy base (any base that has previously been\r\n" +
			"  SCANned or LISTed by anyone on your team).\r\n" +
			"- Location and number of builds of any known planet, or any planet\r\n" +
			"  within range.\r\n" +
			"\r\n" +
			"The above information is also available, in whole or in part, through\r\n" +
			"the SUMMARY, BASES, PLANETS, and TARGETS commands. Each command has\r\n" +
			"it's own default range, side (Federation, Empire, Romulan, Neutral),\r\n" +
			"and object (ship, base, planet). LIST (and SUMMARY) include\r\n" +
			"everything (infinite range, all sides, all objects) by default. On\r\n" +
			"output, enemy objects are flagged with * (star) in column 1 unless the\r\n" +
			"command is TARGETS.\r\n" +
			"\r\n" +
			"Keywords used with BASES, PLANETS, TARGETS, LIST, and SUMMARY (not all\r\n" +
			"keywords are legal for all commands):\r\n" +
			"\r\n" +
			"ship names Include only specified ships (several ship names may\r\n" +
			"                be given, including Romulan).\r\n" +
			"vpos hpos List only the object at the location vpos-hpos.\r\n" +
			"CLosest List only the closest of the specified objects.\r\n" +
			"SHips Include only ships (Federation, Empire, or Romulan).\r\n" +
			"BAses Include only bases (Federation or Empire).\r\n" +
			"PLanets Include only planets (Federation, Empire, or Neutral).\r\n" +
			"POrts Include only bases and planets. If no side is\r\n" +
			"                specified (Federation, Empire, Neutral, or Captured),\r\n" +
			"                include only friendly ports.\r\n" +
			"FEderation Include only Federation forces.\r\n" +
			"HUman Same as Federation.\r\n" +
			"EMpire Include only Empire forces.\r\n" +
			"FRiendly Include only friendly forces (Federation or Empire).\r\n" +
			"ENemy Include only enemy forces (Empire or Federation and\r\n" +
			"                Romulan).\r\n" +
			"TArgets Same as enemy.\r\n" +
			"NEutral Include only neutral planets.\r\n" +
			"CAptured Include only captured planets (Federation or Empire).\r\n" +
			"n Include only objects within n sectors.\r\n" +
			"ALl Include all sides unless a side is explicitly given.\r\n" +
			"                Extend the range to infinity unless a range is\r\n" +
			"                explicitly given.\r\n" +
			"LIst List individual items. Turn off summary unless\r\n" +
			"                command is SUMMARY or the keyword SUMMARY is\r\n" +
			"                specified.\r\n" +
			"SUmmary List summary of all selected items. Turn off list\r\n" +
			"                unless command is LIST or the keyword LIST is\r\n" +
			"                specified. Extend the range to infinity unless a range is\r\n" +
			"                explicitly given.\r\n" +
			"And Used to separate groups of keywords.\r\n" +
			"& Same as AND.\r\n" +
			"\r\n" +
			"Examples:\r\n" +
			"LIST List all information available on all ships, bases,\r\n" +
			"                and planets.\r\n" +
			"LIST SUM List all available info plus a summary of the number\r\n" +
			"                of each object in game.\r\n" +
			"LI EN BA List the location of all known enemy bases.\r\n" +
			"LI SH List all available info on all ships in the game.\r\n" +
			"LI CL PO List closest friendly base or friendly or neutral\r\n" +
			"                planet.\r\n" +
			"LI 1 3 & 9 5 List the objects at locations 1-3 and 9-5.",
	}
	//Move command logic here (using Bresenham's Line Algorithm)
	i.gowarsCommands["move"] = Command{
		Handler: func(args []string, conn net.Conn) string {
			var msg string
			info, ok := i.connections.Load(conn)
			if !ok || info.(ConnectionInfo).Section != "gowars" || info.(ConnectionInfo).Shipname == "" {
				return "You must be in GOWARS with a ship to use this command"
			}
			connInfo := info.(ConnectionInfo)

			// Prompting for shipnames when "move computed ?" is entered
			if len(args) == 2 && args[0] == "computed" && args[1] == "?" {
				info, ok := i.connections.Load(conn)
				if ok {
					connInfo := info.(ConnectionInfo)
					if connInfo.Ship != nil {
						if connInfo.Ship.ComputerDamage > CriticalDamage {
							return "Computer inoperative."
						}
					}
				}
				info, ok = i.connections.Load(conn)
				if !ok {
					return "Connection info not found"
				}
				galaxy := info.(ConnectionInfo).Galaxy

				userSide := ""
				if connInfo.Ship != nil {
					userSide = connInfo.Ship.Side
				}

				var lines []string
				for _, obj := range i.objects {
					if obj.Type == "Ship" && obj.Galaxy == galaxy {
						if (userSide == "federation" && obj.SeenByFed) || (userSide == "empire" && obj.SeenByEmp) {
							lines = append(lines, fmt.Sprintf("move computed %s", obj.Name))
						}
					}
				}
				if len(lines) == 0 {
					return "No ships found in this galaxy."
				}
				return strings.Join(lines, "\r\n")
			}

			options := map[string]bool{"absolute": true, "relative": true, "computed": true}
			moveParams := []string{"absolute", "relative", "computed"}
			for i := range args {
				argLower := strings.ToLower(args[i])
				matches := []string{}
				for _, param := range moveParams {
					if strings.HasPrefix(param, argLower) {
						matches = append(matches, param)
					}
				}
				if len(matches) == 1 {
					args[i] = matches[0]
				}
			}

			params := []string{}
			xArg, yArg := "", ""

			for len(args) > 0 && options[strings.ToLower(args[0])] && len(params) < 4 {
				params = append(params, strings.ToLower(args[0]))
				args = args[1:]
			}

			mode := connInfo.ICdef

			if len(params) > 0 {
				if params[0] == "absolute" || params[0] == "relative" || params[0] == "computed" {
					mode = params[0]
				}
			}
			if mode == "absolute" || mode == "relative" {
				if len(args) > 0 {
					xArg = args[0]
				}
				if len(args) > 1 {
					yArg = args[1]
				}
			} else {
				if mode == "computed" {
					if len(args) == 0 {
						info, ok := i.connections.Load(conn)
						if ok {
							connInfo := info.(ConnectionInfo)
							if connInfo.Ship != nil {
								if connInfo.Ship.ComputerDamage > CriticalDamage {
									return "Computer inoperative."
								}
							}
						}

						info, ok = i.connections.Load(conn)
						if !ok {
							return "Connection info not found"
						}
						galaxy := info.(ConnectionInfo).Galaxy

						var lines []string
						i.connections.Range(func(_, value interface{}) bool {
							connInfo := value.(ConnectionInfo)
							if connInfo.Shipname != "" && connInfo.Galaxy == galaxy {
								lines = append(lines, fmt.Sprintf("move computed %s", connInfo.Shipname))
							}
							return true
						})

						if len(lines) == 0 {
							return "No ships found in this galaxy."
						}
						return strings.Join(lines, "\r\n")
					}
					if len(args) > 0 {
						info, ok := i.connections.Load(conn)
						if ok {
							connInfo := info.(ConnectionInfo)
							if connInfo.Ship != nil {
								if connInfo.Ship.ComputerDamage > CriticalDamage {
									return "Computer inoperative."
								}
							}
						}

						info, _ = i.connections.Load(conn)
						var allShipNames []string
						galaxy := info.(ConnectionInfo).Galaxy
						ships := i.getObjectsByType(galaxy, "Ship")
						if ships != nil {
							for _, obj := range ships {
								allShipNames = append(allShipNames, obj.Name)
							}
						}
						abbrParts := args
						var matchedShips []string
						for _, name := range allShipNames {
							match := true
							searchIdx := 0
							for _, part := range abbrParts {
								partLower := strings.ToLower(part)
								remaining := strings.ToLower(name[searchIdx:])
								if !strings.HasPrefix(remaining, partLower) {
									idx := strings.Index(remaining, partLower)
									if idx != 0 {
										match = false
										break
									}
								}
								searchIdx += len(partLower)
							}
							if match {
								matchedShips = append(matchedShips, name)
							}
						}
						if len(matchedShips) == 1 {
							computedShip := matchedShips[0]
							for _, obj := range i.objects {
								if obj.Type == "Ship" && obj.Galaxy == info.(ConnectionInfo).Galaxy && obj.Name == computedShip {
									xArg = strconv.Itoa(obj.LocationX)
									yArg = strconv.Itoa(obj.LocationY)
								}
							}
						} else if len(matchedShips) == 0 {
							return "<shipname> not found"
						} else {
							return "Ambiguous shipname abbreviation"
						}
					}
				} else {
					return fmt.Sprintf("<shipname> is required")
				}
			}

			if mode == "computed" {
				if xArg == "" {
					return fmt.Sprintf("<shipname> is required")
				}
			} else {
				if mode == "absolute" || mode == "relative" {
					if xArg == "" || yArg == "" {
						return "<vpos> <hpos> are required"
					}
				}
			}
			var targetX int
			var targetY int
			var err error
			if mode == "absolute" || mode == "relative" {
				targetX, targetY, err = i.parseCoordinates(xArg, yArg, conn, false)
				if err != nil {
					return err.Error()
				}
			}

			targetX, _ = strconv.Atoi(xArg)
			targetY, _ = strconv.Atoi(yArg)
			if mode == "computed" {
				_, _, ok := i.getShipLocation(conn)
				if !ok {
					return "Cannot find ship location"
				}
			} else {
				if mode == "relative" {
					startX, startY, ok := i.getShipLocation(conn)

					if !ok {
						return "Cannot find ship location"
					}
					targetX = startX + targetX
					targetY = startY + targetY
				}
			}

			if targetX < BoardStart || targetX > MaxSizeX {
				return fmt.Sprintf("X coordinate lies outside galaxy.")
			}
			if targetY < BoardStart || targetY > MaxSizeY {
				return fmt.Sprintf("Y coordinate lies outside galaxy.")
			}

			ship := connInfo.Ship
			if ship == nil {
				return "You do not have a ship."
			}

			msg, dlypse, err := i.moveShip(ship, targetX, targetY, mode, &connInfo)

			if err != nil {
				return msg
			}

			destructionMsg := i.delayPause(conn, dlypse, connInfo.Galaxy, connInfo.Ship.Type, connInfo.Ship.Side)
			return msg + destructionMsg
		},
		Help: "MOVE using warp drive\r\n" +
			"Syntax: Move [Absolute|Relative|Computed] <vpos> <hpos>\r\n" +
			"\r\n" +
			"Maximum speed is warp factor 6, which will move you 6 sectors per\r\n" +
			"turn. Maximum SAFE speed is warp factor 4; warp factors 5 and 6 risk\r\n" +
			"potential warp engine damage. Energy consumption per move is\r\n" +
			"proportional to the square of the warp factor. If the ship's shields\r\n" +
			"are up during this movement, the energy consumption is doubled.\r\n" +
			"Moving changes your ship's condition to green.\r\n" +
			"\r\n" +
			"Examples:\r\n" +
			"M 37 45                 Move to sector 37-45.\r\n" +
			"M A 37 45               Equivalent to \"M 37 45\".\r\n" +
			"M R 4 -5                Move to sector 37-45, if your present location is\r\n" +
			"                        33-50 (move up 4 sectors and left 5 sectors).\r\n" +
			"M C W \"Ram\"             the Wolf. No actual collision occurs, but your\r\n" +
			"                        ship ends up adjacent to the Wolf's current position.",
	}
	i.gowarsCommands["help"] = Command{
		Handler: func(args []string, conn net.Conn) string {
			if len(args) == 0 || (len(args) > 0 && args[0] == "*") {
				keys := make([]string, 0, len(i.gowarsCommands))
				for cmd := range i.gowarsCommands {
					if cmd != "?" {
						keys = append(keys, cmd)
					}
				}
				sort.Strings(keys)
				var lines []string
				if DecwarMode {
					lines = append(lines, "Decwars commands:")
				} else {
					lines = append(lines, "GOWARS commands:")
				}
				for idx := 0; idx < len(keys); idx += 6 {
					end := idx + 6
					if end > len(keys) {
						end = len(keys)
					}
					row := keys[idx:end]
					padded := make([]string, 6)
					for j := 0; j < 6; j++ {
						if j < len(row) {
							padded[j] = fmt.Sprintf("%-13s", i.getAbbreviation(row[j], keys))
						} else {
							padded[j] = strings.Repeat(" ", 13)
						}
					}
					lines = append(lines, strings.Join(padded, ""))
				}

				// Update galaxy tracker
				if info, ok := i.connections.Load(conn); ok {
					connInfo := info.(ConnectionInfo)
					i.trackerMutex.Lock()
					if tracker, exists := i.galaxyTracker[connInfo.Galaxy]; exists {
						tracker.LastActive = time.Now()
						i.galaxyTracker[connInfo.Galaxy] = tracker
					} else {
						now := time.Now()
						i.galaxyTracker[connInfo.Galaxy] = GalaxyTracker{GalaxyStart: now, LastActive: now}
					}
					i.trackerMutex.Unlock()
				}

				return strings.Join(lines, "\r\n")
			}
			target := strings.ToLower(args[0])
			fullCmd, ok := i.resolveCommand(target, "gowars")
			if !ok {
				if DecwarMode {
					return "Invalid Decwar command: " + target
				} else {
					return "Invalid GOWARS command:" + target
				}
			}

			// Update galaxy tracker
			if info, ok := i.connections.Load(conn); ok {
				connInfo := info.(ConnectionInfo)
				i.trackerMutex.Lock()
				if tracker, exists := i.galaxyTracker[connInfo.Galaxy]; exists {
					tracker.LastActive = time.Now()
					i.galaxyTracker[connInfo.Galaxy] = tracker
				} else {
					now := time.Now()
					i.galaxyTracker[connInfo.Galaxy] = GalaxyTracker{GalaxyStart: now, LastActive: now}
				}
				i.trackerMutex.Unlock()
			}

			return fmt.Sprintf("Command: %s\r\nDescription: %s", fullCmd, i.gowarsCommands[fullCmd].Help)
		},
		Help: "Without parameter: list all GOWARS commands in 4 columns; with parameter: show detailed help for that command\r\n\r\n" +
			"Special characters:\r\n" +
			"Enter  (ASCII 13)   Submit command.\r\n" +
			"Backspace(ASCII 8)  Delete last character.\r\n" +
			"Ctrl+A (ASCII 1):   Move cursor to beginning of line.\r\n" +
			"Ctrl+B (ASCII 2):   Move cursor left.\r\n" +
			"Ctrl+C (ASCII 3):   Cancel command queue and interrupt output.\r\n" +
			"Ctrl+D (ASCII 4):   Signals end-of-file input (EOF).\r\n" +
			"Ctrl+E (ASCII 5):   Move cursor to end of line.\r\n" +
			"Ctrl+F (ASCII 6):   Move cursor right.\r\n" +
			"Ctrl+K (ASCII 11):  Delete to end of line.\r\n" +
			"Ctrl+L (ASCII 12):  Clears the terminal screen.\r\n" +
			// "Ctrl+S (ASCII 19): Halts terminal output (XOFF).\r\n" +
			// "Ctrl+Q (ASCII 17): Resumes terminal output (XON).\r\n" +
			"Ctrl+U (ASCII 21):  Clear entire line.\r\n" +
			"Ctrl+W (ASCII 23):  Delete last word (unsupported on web client)\r\n" +
			"Tab    (ASCII 9):   Command/parameter completion.\r\n" +
			"?      (ASCII 63):  Help and prompting.\r\n" +
			"Escape (ASCII 27):  Command completion or repeat last command.\r\n",
	}
	i.gowarsCommands["?"] = Command{
		Handler: i.gowarsCommands["help"].Handler,
		Help:    "Alias for 'help' in GOWARS",
	}

	// Add stubs for new gowars-only commands
	i.gowarsCommands["admin"] = Command{
		Handler: func(args []string, conn net.Conn) string {
			if len(args) == 0 {
				return adminHelpText
			}

			// List of valid parameters for abbreviation resolution
			adminParams := []string{
				"shieldsdamage",
				"warpdamage",
				"impulsedamage",
				"lifesupport",
				"torpdamage",
				"phaserdamage",
				"computerdamage",
				"radiodamage",
				"tractordamage",
				"shieldenergy",
				"shipenergy",
				"numtorps",
				"shipdamage",
				"shipcondition",
				"password",
				"create",
				"beam",
				"status",
				"damages",
				"runtime",
				"side",
			}

			paramInput := strings.ToLower(args[0])
			// Resolve abbreviation for parameter
			param := ""
			for _, p := range adminParams {
				if strings.HasPrefix(p, paramInput) {
					if param == "" {
						param = p
					} else {
						// Ambiguous abbreviation
						return "Error: ambiguous parameter abbreviation '" + paramInput + "'"
					}
				}
			}
			if param == "" {
				return "Unknown admin parameter: " + paramInput
			}

			// Admin create command
			if param == "create" {
				if len(args) < 4 {
					return "Error: admin create requires three parameters: <object type> <vpos> <hpos>"
				}

				infoRaw, ok := i.connections.Load(conn)
				if !ok {
					return "Error: could not find your connection info"
				}
				connInfo := infoRaw.(ConnectionInfo)
				if !connInfo.AdminMode {
					return "Error: you must enter the admin password first"
				}

				// Resolve object type abbreviation
				objectTypeInput := strings.ToLower(args[1])
				objectTypes := []string{"star", "planet", "base", "blackhole", "romulan"}
				objectType := ""
				for _, ot := range objectTypes {
					if strings.HasPrefix(ot, objectTypeInput) {
						if objectType == "" {
							objectType = ot
						} else {
							// Ambiguous abbreviation
							return "Error: ambiguous object type abbreviation '" + objectTypeInput + "'"
						}
					}
				}
				if objectType == "" {
					return "Error: unknown object type '" + objectTypeInput + "'. Valid types: star, planet, base, blackhole, romulan"
				}

				// Parse coordinates using ICDEF setting
				x, y, err := i.parseCoordinates(args[2], args[3], conn, false)
				if err != nil {
					return "Error: " + err.Error()
				}

				// Check if coordinates are within bounds
				if x < 1 || x > MaxSizeX || y < 1 || y > MaxSizeY {
					return fmt.Sprintf("Error: coordinates (%d, %d) are outside galaxy bounds (1-20, 1-20)", x, y)
				}

				galaxy := connInfo.Galaxy

				// Check if location is already occupied
				existingObj := i.getObjectAtLocation(galaxy, x, y)
				if existingObj != nil {
					return fmt.Sprintf("Error: location (%d, %d) is already occupied by %s", x, y, existingObj.Type)
				}

				// Create the new object
				var newObj Object
				var objName string
				var objSide string

				// Set object type and related properties
				switch objectType {
				case "star":
					newObj.Type = "Star"
					objSide = "neutral"
					objName = "Star"
				case "planet":
					newObj.Type = "Planet"
					objSide = "neutral"
					objName = "Planet"
				case "base":
					newObj.Type = "Base"
					objSide = "federation" // Default to federation, could be made configurable
					objName = "Base"
				case "blackhole":
					newObj.Type = "Black Hole"
					objSide = "neutral"
					objName = "Black Hole"
				case "romulan":
					newObj.Type = "Ship"
					objSide = "romulan"
					// Generate a unique Romulan name to avoid collisions in shipsByGalaxyAndName
					numRomulans := 0
					for _, o := range i.objects {
						if o.Galaxy == connInfo.Galaxy && o.Type == "Ship" && o.Side == "romulan" {
							numRomulans++
						}
					}
					objName = fmt.Sprintf("Romulan%d", numRomulans+1)
				}

				newObj.Galaxy = galaxy
				newObj.LocationX = x
				newObj.LocationY = y
				newObj.Side = objSide
				newObj.Name = objName
				newObj.Shields = InitialShieldValue - 1
				if objectType == "romulan" {
					newObj.Shields = InitialShieldValue
					newObj.ShieldsUpDown = true
				}
				newObj.Condition = "Green"
				newObj.TorpedoTubes = func() int {
					if objectType == "romulan" {
						return math.MaxInt
					}
					return 10
				}()
				newObj.TorpedoTubeDamage = 0
				newObj.PhasersDamage = 0
				newObj.ComputerDamage = 0
				newObj.LifeSupportDamage = 0
				newObj.LifeSupportReserve = 5
				newObj.RadioOnOff = true
				newObj.RadioDamage = 0
				newObj.TractorOnOff = false
				newObj.TractorShip = ""
				newObj.TractorDamage = 0
				newObj.ShipEnergy = InitialShipEnergy
				newObj.SeenByFed = false
				newObj.SeenByEmp = false
				newObj.TotalShipDamage = 0
				newObj.WarpEnginesDamage = 0
				newObj.Builds = 0

				// Set visibility for bases
				if newObj.Type == "Base" {
					if newObj.Side == "federation" {
						newObj.SeenByFed = true
					} else if newObj.Side == "empire" {
						newObj.SeenByEmp = true
					}
				}

				i.addObjectToObjects(newObj)
				return fmt.Sprintf("Admin create: %s created at (%d, %d)", newObj.Type, x, y)
			}

			// Admin beam command
			if param == "beam" {
				if len(args) < 5 {
					return "Error: admin beam requires four parameters: <obj-vpos> <obj-hpos> <vpos> <hpos>"
				}
				objVpos, errObjV := strconv.Atoi(args[1])
				objHpos, errObjH := strconv.Atoi(args[2])
				newVpos, errNewV := strconv.Atoi(args[3])
				newHpos, errNewH := strconv.Atoi(args[4])
				if errObjV != nil || errObjH != nil || errNewV != nil || errNewH != nil {
					return "Error: admin beam parameters must be integers"
				}
				infoRaw, ok := i.connections.Load(conn)
				if !ok {
					return "Error: could not find your connection info"
				}
				connInfo := infoRaw.(ConnectionInfo)
				if !connInfo.AdminMode {
					return "Error: you must enter the admin password first"
				}
				galaxy := connInfo.Galaxy
				obj := i.getObjectAtLocation(galaxy, objVpos, objHpos)
				if obj == nil {
					return "Error: no object found at source coordinates (" + strconv.Itoa(objVpos) + ", " + strconv.Itoa(objHpos) + ")"
				}
				// Validate galaxy boundaries for admin beam
				isValid, maxX, maxY := i.validateGalaxyBoundaries(connInfo.Galaxy, newVpos, newHpos)
				if !isValid {
					return fmt.Sprintf("Admin beam: coordinates (%d, %d) are outside galaxy boundaries (1,1 to %d,%d)",
						newVpos, newHpos, maxX, maxY)
				}

				i.updateObjectLocation(obj, newVpos, newHpos)
				return "Admin beam: object moved from (" + strconv.Itoa(objVpos) + ", " + strconv.Itoa(objHpos) + ") to (" + strconv.Itoa(newVpos) + ", " + strconv.Itoa(newHpos) + ")"
			}
			//
			// Admin status command
			if param == "status" {
				if len(args) < 3 {
					return "Error: admin status requires two parameters: X and Y"
				}
				x, y, err := i.parseCoordinates(args[1], args[2], conn, false)
				if err != nil {
					return "Error: " + err.Error()
				}
				infoRaw, ok := i.connections.Load(conn)
				if !ok {
					return "Error: could not find your connection info"
				}
				connInfo := infoRaw.(ConnectionInfo)
				if !connInfo.AdminMode {
					return "Error: you must enter the admin password first"
				}
				galaxy := connInfo.Galaxy

				// Find object at specified coordinates
				var targetObject *Object
				// Use spatial indexing for direct lookup
				targetObject = i.getObjectAtLocation(galaxy, x, y)

				if targetObject == nil {
					return fmt.Sprintf("No object found at coordinates (%d, %d)", x, y)
				}

				// Generate status output - always show all standard fields
				var sb strings.Builder

				// Object Type
				sb.WriteString(fmt.Sprintf("Object Type \t%s\r\n", targetObject.Type))

				// Location
				sb.WriteString(fmt.Sprintf("Location \t%d-%d\r\n", targetObject.LocationX, targetObject.LocationY))

				// Galaxy
				sb.WriteString(fmt.Sprintf("Galaxy \t\t%d\r\n", targetObject.Galaxy))

				if targetObject.Type == "Planet" {
					sb.WriteString(fmt.Sprintf("Builds \t\t%d\r\n", targetObject.Builds))
				}

				// Name
				name := targetObject.Name
				if name == "" {
					name = "<none>"
				}
				sb.WriteString(fmt.Sprintf("Name \t\t%s\r\n", name))

				// Side
				side := targetObject.Side
				if side == "" {
					side = "<none>"
				}
				sb.WriteString(fmt.Sprintf("Side \t\t%s\r\n", side))

				// Stardate
				sb.WriteString(fmt.Sprintf("Stardate \t%d\r\n", targetObject.StarDate))

				// Condition
				condition := targetObject.Condition
				if condition == "" {
					condition = "<none>"
				}
				sb.WriteString(fmt.Sprintf("Condition \t%s\r\n", condition))

				// Torpedoes
				sb.WriteString(fmt.Sprintf("Torpedoes \t%d\r\n", targetObject.TorpedoTubes))

				// Energy
				energy := fmt.Sprintf("        %.1f", float64(targetObject.ShipEnergy)/10.0)
				sb.WriteString(fmt.Sprintf("Energy \t%s\r\n", energy))

				// Shields
				shieldPct := float64(targetObject.Shields) / float64(InitialShieldValue) * 100.0
				shieldStr := fmt.Sprintf("%.0f%%", shieldPct)
				shieldudflag := "-"
				if targetObject.ShieldsUpDown == true {
					shieldudflag = "+"
				}
				shieldStr = shieldudflag + shieldStr + " " + fmt.Sprintf("%.1f", float64(targetObject.Shields)/10.0)
				sb.WriteString(fmt.Sprintf("Shields \t%s\r\n", shieldStr))

				// ShieldsUpDown
				shieldsUpDown := "Down"
				if targetObject.ShieldsUpDown {
					shieldsUpDown = "Up"
				}
				sb.WriteString(fmt.Sprintf("ShieldsUpDown \t%s\r\n", shieldsUpDown))

				// Radio
				radio := "Off"
				if targetObject.RadioOnOff {
					radio = "On"
				}
				sb.WriteString(fmt.Sprintf("Radio \t\t%s\r\n", radio))

				// Damage
				sb.WriteString(fmt.Sprintf("Damage \t\t%d\r\n", targetObject.TotalShipDamage))

				return fmt.Sprintf("Status for %s at (%d, %d):\r\n%s", targetObject.Type, x, y, sb.String())
			}
			//
			// Admin damages command
			if param == "damages" {
				if len(args) < 3 {
					return "Error: admin damages requires two parameters: X and Y"
				}
				x, y, err := i.parseCoordinates(args[1], args[2], conn, false)
				if err != nil {
					return "Error: " + err.Error()
				}
				infoRaw, ok := i.connections.Load(conn)
				if !ok {
					return "Error: could not find your connection info"
				}
				connInfo := infoRaw.(ConnectionInfo)
				if !connInfo.AdminMode {
					return "Error: you must enter the administrator password first"
				}
				galaxy := connInfo.Galaxy

				// Find object at specified coordinates
				var targetObject *Object
				// Use spatial indexing for direct lookup
				targetObject = i.getObjectAtLocation(galaxy, x, y)

				if targetObject == nil {
					return fmt.Sprintf("No object found at coordinates (%d, %d)", x, y)
				}

				// Generate damages output - always show all damage fields
				var sb strings.Builder

				// Deflector Shields
				sb.WriteString(fmt.Sprintf("Deflector Shields: %d\r\n", targetObject.ShieldsDamage))

				// Warp Engines
				sb.WriteString(fmt.Sprintf("Warp Engines: %d\r\n", targetObject.WarpEnginesDamage))

				// Impulse Engines
				sb.WriteString(fmt.Sprintf("Impulse Engines: %d\r\n", targetObject.ImpulseEnginesDamage))

				// Life Support
				sb.WriteString(fmt.Sprintf("Life Support: %d\r\n", targetObject.LifeSupportDamage))

				// Torpedo Tubes
				sb.WriteString(fmt.Sprintf("Torpedo Tubes: %d\r\n", targetObject.TorpedoTubeDamage))

				// Phasers
				sb.WriteString(fmt.Sprintf("Phasers: %d\r\n", targetObject.PhasersDamage))

				// Computer
				sb.WriteString(fmt.Sprintf("Computer: %d\r\n", targetObject.ComputerDamage))

				// Radio
				sb.WriteString(fmt.Sprintf("Radio: %d\r\n", targetObject.RadioDamage))

				// Tractor Beam
				sb.WriteString(fmt.Sprintf("Tractor Beam: %d\r\n", targetObject.TractorDamage))

				return fmt.Sprintf("Damages for %s at (%d, %d):\r\n%s", targetObject.Type, x, y, sb.String())
			}
			//
			// Administrator runtime command
			if param == "runtime" {
				infoRaw, ok := i.connections.Load(conn)
				if !ok {
					return "Error: could not find your connection info"
				}
				connInfo := infoRaw.(ConnectionInfo)
				if !connInfo.AdminMode {
					return "Error: you must enter the administrator password first"
				}

				// Get memory statistics
				var memStats runtime.MemStats
				runtime.ReadMemStats(&memStats)

				// Get other runtime information
				numCPU := runtime.NumCPU()
				numGoroutines := runtime.NumGoroutine()
				version := runtime.Version()

				var sb strings.Builder
				sb.WriteString("Go Runtime Statistics:\r\n")
				sb.WriteString(fmt.Sprintf("Go Version: %s\r\n", version))
				sb.WriteString(fmt.Sprintf("Number of CPUs: %d\r\n", numCPU))
				sb.WriteString(fmt.Sprintf("Number of Goroutines: %d\r\n", numGoroutines))
				sb.WriteString("\r\nMemory Statistics:\r\n")
				sb.WriteString(fmt.Sprintf("Allocated Memory: %.2f MB\r\n", float64(memStats.Alloc)/1024/1024))
				sb.WriteString(fmt.Sprintf("Total Allocated: %.2f MB\r\n", float64(memStats.TotalAlloc)/1024/1024))
				sb.WriteString(fmt.Sprintf("System Memory: %.2f MB\r\n", float64(memStats.Sys)/1024/1024))
				sb.WriteString(fmt.Sprintf("Heap Objects: %d\r\n", memStats.HeapObjects))
				sb.WriteString(fmt.Sprintf("GC Runs: %d\r\n", memStats.NumGC))
				sb.WriteString(fmt.Sprintf("Last GC Time: %v\r\n", time.Unix(0, int64(memStats.LastGC))))

				return sb.String()
			}

			//
			if len(args) < 2 {
				return "Error: missing value for " + param
			}
			value := args[1]
			if param == "password" {
				if value != "*MINK" {
					return "NOT an Administrator: " + value
				} else {
					infoRaw, ok := i.connections.Load(conn)
					if ok {
						info := infoRaw.(ConnectionInfo)
						info.AdminMode = true
						i.connections.Store(conn, info)
					}
					return "Administrator mode on"
				}
			}
			// Require AdminMode to be true for all administrator parameters except password
			infoRaw, ok := i.connections.Load(conn)
			if !ok {
				return "Error: could not find your connection info"
			}
			connInfo := infoRaw.(ConnectionInfo)
			if !connInfo.AdminMode {
				return "Error: you must enter the administrator password first"
			}

			var valInt int
			var valFloat float64
			if param == "shipcondition" {
				allowed := map[string]bool{"green": true, "red": true, "yellow": true}
				valLower := strings.ToLower(value)
				if !allowed[valLower] {
					return "Error: ShipCondition must be Green, Red, or Yellow"
				}
				// Capitalize first letter
				value = strings.Title(valLower)
			} else if param == "side" {
				allowedSides := map[string]bool{
					"federation": true,
					"empire":     true,
					"romulan":    true,
					"neutral":    true,
				}
				valLower := strings.ToLower(value)
				if !allowedSides[valLower] {
					return "Error: Side must be federation, empire, romulan, or neutral"
				}
				value = valLower
			} else {
				// numtorps must be a whole number; all other numeric fields accept decimals
				// so callers can enter display-scale values (e.g. "10.5" for a damage field).
				if param == "numtorps" {
					var err error
					valInt, err = strconv.Atoi(value)
					if err != nil {
						return "Error: NumTorps value must be an integer"
					}
					valFloat = float64(valInt)
				} else {
					var err error
					valFloat, err = strconv.ParseFloat(value, 64)
					if err != nil {
						return "Error: value must be a number"
					}
					// valInt is used by shipcondition/side fall-throughs; set a
					// rounded version as a sane default. Damage/energy cases below
					// compute their own scaled int directly from valFloat.
					valInt = int(math.Round(valFloat))
				}
			}
			shipname := connInfo.Shipname
			galaxy := connInfo.Galaxy
			if shipname == "" {
				return "Error: you must have a ship to use administrator commands"
			}

			found := false
			for idx := range i.objects {
				obj := i.objects[idx]
				if obj.Type == "Ship" && obj.Name == shipname && obj.Galaxy == galaxy {
					found = true
					switch param {
					case "shieldsdamage":
						// Device damage stored at 100x display scale; accept display units with decimals
						obj.ShieldsDamage = int(math.Round(valFloat * 100))
						return "Set ShieldsDamage for your ship to " + value
					case "warpdamage":
						obj.WarpEnginesDamage = int(math.Round(valFloat * 100))
						return "Set WarpDamage for your ship to " + value
					case "impulsedamage":
						obj.ImpulseEnginesDamage = int(math.Round(valFloat * 100))
						return "Set ImpulseDamage for your ship to " + value
					case "lifesupport":
						obj.LifeSupportDamage = int(math.Round(valFloat * 100))
						return "Set LifeSupport for your ship to " + value
					case "torpdamage":
						obj.TorpedoTubeDamage = int(math.Round(valFloat * 100))
						return "Set TorpDamage for your ship to " + value
					case "phaserdamage":
						obj.PhasersDamage = int(math.Round(valFloat * 100))
						return "Set PhaserDamage for your ship to " + value
					case "computerdamage":
						obj.ComputerDamage = int(math.Round(valFloat * 100))
						return "Set ComputerDamage for your ship to " + value
					case "radiodamage":
						obj.RadioDamage = int(math.Round(valFloat * 100))
						return "Set RadioDamage for your ship to " + value
					case "tractordamage":
						obj.TractorDamage = int(math.Round(valFloat * 100))
						return "Set TractorDamage for your ship to " + value
					case "shipdamage":
						// TotalShipDamage stored at 100x display scale; accept display units with decimals
						obj.TotalShipDamage = int(math.Round(valFloat * 100))
						return "Set ShipDamage (total ship damage) for your ship to " + value
					case "shipcondition":
						obj.Condition = value
						return "Set ShipCondition for your ship to " + obj.Condition
					case "side":
						obj.Side = value
						return "Set Side for your ship to " + value
					case "shieldenergy":
						// Shields stored at 10x display scale; accept display units with decimals
						obj.Shields = int(math.Round(valFloat * 10))
						return "Set ShieldEnergy for your ship to " + value
					case "shipenergy":
						// ShipEnergy stored at 10x display scale; accept display units with decimals
						obj.ShipEnergy = int(math.Round(valFloat * 10))
						return "Set ShipEnergy for your ship to " + value
					case "numtorps":
						obj.TorpedoTubes = valInt
						return "Set NumTorps for your ship to " + value
					default:
						return "Unknown administrator parameter: " + param
					}
				}
			}
			if !found {
				return "Error: your ship was not found in the current galaxy"
			}
			return "Error: failed to set parameter"
		},
		Help: "Administrator command for setting ship system damage/status or password.\r\n" +
			"Parameters:\r\n" +
			"  ShieldsDamage <value>      - Set shields damage\r\n" +
			"  WarpDamage <value>         - Set warp engines damage\r\n" +
			"  ImpulseDamage <value>      - Set impulse engines damage\r\n" +
			"  LifeSupport <value>        - Set life support damage\r\n" +
			"  TorpDamage <value>         - Set torpedo tube damage\r\n" +
			"  PhaserDamage <value>       - Set phaser damage\r\n" +
			"  ComputerDamage <value>     - Set computer damage\r\n" +
			"  RadioDamage <value>        - Set radio damage\r\n" +
			"  TractorDamage <value>      - Set tractor damage\r\n" +
			"  ShipDamage <value>         - Set total ship damage\r\n" +
			"  ShipCondition <value>      - Set ship condition (Green, Red, Yellow)\r\n" +
			"  Side <side>                - Change your ship's side (federation, empire, romulan, neutral)\r\n" +
			"  Password <string value>    - Enter administrator password\r\n" +
			"  ShieldEnergy <value>       - Set shield energy\r\n" +
			"  ShipEnergy <value>         - Set ship energy\r\n" +
			"  NumTorps <value>           - Set number of torpedos\r\n" +
			"  Create <type> <vpos> <hpos> - Create object at coordinates (uses ICdef)\r\n" +
			"  Move <X> <Y>               - Move your ship to coordinates X,Y\r\n" +
			"  Beam <x><y> <newx><newy>   - Beam an object from 1 place to another\r\n" +
			"  Status <X> <Y>             - Show status of object at coordinates X,Y\r\n" +
			"  Damages <X> <Y>            - Show damage status of object at coordinates X,Y\r\n" +
			"  Runtime                    - Show Go runtime statistics\r\n" +
			"Object types for Create: star, planet, base, blackhole, romulan (can be abbreviated)\r\n" +
			"Example: administrator ShieldsDamage 10\r\n" +
			"Example: administrator ShieldEn 500\r\n" +
			"Example: administrator ShipDamage 300\r\n" +
			"Example: administrator ShipCondition Green\r\n" +
			"Example: administrator Side federation\r\n" +
			"Example: administrator Password YourBestGuess\r\n" +
			"Example: administrator Move 12 34\r\n" +
			"Example: administrator Status 12 34\r\n" +
			"Example: administrator Damages 12 34\r\n" +
			"Example: administrator Runtime",
	}
	i.gowarsCommands["bases"] = Command{
		Handler: func(args []string, conn net.Conn) string {
			info, ok := i.connections.Load(conn)
			if !ok || info.(ConnectionInfo).Shipname == "" {
				return "Error: you must be in GOWARS with a shipname to use bases"
			}

			// If no parameters provided, execute equivalent of "bases sum"
			if len(args) == 0 {
				// Call the list command with "friendly bases summary" parameters
				return i.gowarsCommands["list"].Handler([]string{"friendly", "bases", "summary"}, conn)
			}

			// Define valid parameters
			validParams := map[string]bool{
				"enemy":   true,
				"sum":     true,
				"all":     true,
				"closest": true,
			}

			// Parse coordinates if provided
			hasCoords := false
			var targetX, targetY int
			if len(args) >= 2 {
				vpos, err1 := strconv.Atoi(args[0])
				hpos, err2 := strconv.Atoi(args[1])
				if err1 == nil && err2 == nil {
					targetX, targetY = vpos, hpos
					hasCoords = true
					args = args[2:] // Remove coordinates from args
				}
			}

			// Resolve parameter abbreviations
			showEnemy := false
			showSummary := false
			showAll := false
			showClosest := false

			for _, arg := range args {
				param, ok := i.resolveParameter(arg, validParams)
				if ok {
					switch param {
					case "enemy":
						showEnemy = true
					case "sum":
						showSummary = true
					case "all":
						showAll = true
					case "closest":
						showClosest = true
					}
				} else if arg != "" {
					// If parameter doesn't match any valid option, return error
					return fmt.Sprintf("Error: invalid parameter '%s'", arg)
				}
			}

			// Handle coordinates case - check if a base exists at the location
			if hasCoords {
				connInfo := info.(ConnectionInfo)
				galaxy := connInfo.Galaxy
				senderSide, ok := i.getShipSide(conn)
				if !ok {
					return "Error: unable to determine your side"
				}

				// Search for a base at the specified coordinates handle icdef first
				if connInfo.ICdef == "relative" {
					shipX, shipY, ok := i.getShipLocation(conn)
					if ok {
						targetX = targetX + shipX
						targetY = targetY + shipY
					} else {
						return "Error: unable to find your ship"
					}
				}

				var baseFound bool
				var baseObj Object
				bases := i.getObjectsByType(galaxy, "Base")
				if bases != nil {
					for _, obj := range bases {
						if obj.LocationX == targetX && obj.LocationY == targetY {
							baseFound = true
							baseObj = *obj
							break
						}
					}
				}

				if baseFound {
					// Format and return the base information similar to list command output
					senderX, senderY, _ := i.getShipLocation(conn)
					rx := baseObj.LocationX - senderX
					ry := baseObj.LocationY - senderY

					// Format base representation based on output state
					nameOrType := "Base"
					if info, ok := i.connections.Load(conn); ok {
						connInfo := info.(ConnectionInfo)
						if connInfo.OutputState == "medium" || connInfo.OutputState == "short" {
							if baseObj.Side == "federation" {
								nameOrType = "[]"
							} else if baseObj.Side == "empire" {
								nameOrType = "()"
							}
						}
					}

					// Format side representation
					abbr := ""
					if info, ok := i.connections.Load(conn); ok {
						connInfo := info.(ConnectionInfo)
						if connInfo.OutputState != "medium" && connInfo.OutputState != "short" {
							switch baseObj.Side {
							case "federation":
								abbr = "Fed"
							case "empire":
								abbr = "Emp"
							case "neutral":
								abbr = "Neu"
							case "romulan":
								abbr = "Rom"
							default:
								abbr = baseObj.Side
							}
						}
					}

					// Format enemy/friendly marker
					prefix := " "
					if baseObj.Side != senderSide && baseObj.Side != "neutral" {
						prefix = "*"
					}

					// Format coordinates based on OCdef setting
					var locationStr, rangeStr string
					if info, ok := i.connections.Load(conn); ok {
						connInfo := info.(ConnectionInfo)
						switch connInfo.OCdef {
						case "absolute":
							locationStr = fmt.Sprintf("@%d-%d", baseObj.LocationX, baseObj.LocationY)
							rangeStr = ""
						case "relative":
							locationStr = fmt.Sprintf("%+d,%+d", rx, ry)
							rangeStr = ""
						case "both":
							locationStr = fmt.Sprintf("@%d-%d", baseObj.LocationX, baseObj.LocationY)
							rangeStr = fmt.Sprintf("%+d,%+d", rx, ry)
						default: // Default to relative
							locationStr = fmt.Sprintf("%+d,%+d", rx, ry)
							rangeStr = ""
						}
					} else {
						locationStr = fmt.Sprintf("%+d,%+d", rx, ry)
						rangeStr = ""
					}

					shieldPct := float64(baseObj.Shields) / float64(InitialShieldValue) * 100.0
					shieldStr := fmt.Sprintf("%.0f%%", float64(shieldPct))
					//					shieldudflag := "-"
					//					if obj.ShieldsUpDown == true {
					//						shieldudflag = "+"
					//					}
					//					shieldStr = shieldudflag + shieldStr

					// Create output string with the base information
					return prefix + fmt.Sprintf("%-3s %-11s %-8s %-8s %s",
						abbr,
						nameOrType,
						locationStr,
						rangeStr,
						shieldStr)
				} else {
					return fmt.Sprintf("No base found at coordinates %d-%d", targetX, targetY)
				}
			}

			// Handle "bases enemy" command - show known enemy bases AND total count of all enemy bases in game
			if showEnemy && !showSummary && !showAll && !showClosest && !hasCoords {
				// Get listing of known enemy bases from the list command (without summary to avoid filtered count)
				knownListing := i.gowarsCommands["list"].Handler([]string{"enemy", "bases"}, conn)

				// Compute total count of ALL enemy bases in the game
				connInfo := info.(ConnectionInfo)
				galaxy := connInfo.Galaxy
				senderSide, ok := i.getShipSide(conn)
				if !ok {
					return "Error: unable to determine your side"
				}

				enemyBaseCount := 0
				bases := i.getObjectsByType(galaxy, "Base")
				if bases != nil {
					for _, obj := range bases {
						if obj.Side != senderSide && obj.Side != "neutral" {
							enemyBaseCount++
						}
					}
				}

				enemySideName := "Empire"
				if senderSide == "empire" {
					enemySideName = "Federation"
				}

				totalLine := fmt.Sprintf("%2d %s bases in game", enemyBaseCount, enemySideName)

				if knownListing != "" {
					return knownListing + "\r\n" + totalLine
				}
				return totalLine
			}

			// Handle "bases sum" command - show only total number of friendly bases
			if showSummary && !showEnemy && !showAll && !showClosest && !hasCoords {
				connInfo := info.(ConnectionInfo)
				galaxy := connInfo.Galaxy
				senderSide, ok := i.getShipSide(conn)
				if !ok {
					return "Error: unable to determine your side"
				}

				friendlyBaseCount := 0
				bases := i.getObjectsByType(galaxy, "Base")
				if bases != nil {
					for _, obj := range bases {
						if obj.Side == senderSide {
							friendlyBaseCount++
						}
					}
				}

				sideName := "Federation"
				if senderSide == "empire" {
					sideName = "Empire"
				}

				if friendlyBaseCount == 0 {
					return "No friendly bases found in galaxy"
				}
				return fmt.Sprintf("%2d %s bases in game", friendlyBaseCount, sideName)
			}

			// Handle "bases closest" command - call "list closest base"
			if showClosest && !showEnemy && !showSummary && !showAll && !hasCoords {
				return i.gowarsCommands["list"].Handler([]string{"closest", "base"}, conn)
			}

			// Handle "bases all summary" command - show only summary counts
			if showAll && showSummary && !showEnemy && !showClosest && !hasCoords {
				// Get counts directly without individual listings
				info, ok := i.connections.Load(conn)
				if !ok {
					return "Error: connection info not found"
				}
				connInfo := info.(ConnectionInfo)
				galaxy := connInfo.Galaxy

				federationBases := 0
				empireBases := 0
				bases := i.getObjectsByType(galaxy, "Base")
				if bases != nil {
					for _, obj := range bases {
						if obj.Side == "federation" {
							federationBases++
						} else if obj.Side == "empire" {
							empireBases++
						}
					}
				}

				var lines []string
				if federationBases > 0 {
					lines = append(lines, fmt.Sprintf("%2d Federation bases in game", federationBases))
				}
				if empireBases > 0 {
					lines = append(lines, fmt.Sprintf("%2d Empire bases in game", empireBases))
				}
				if len(lines) == 0 {
					lines = append(lines, "No bases found in galaxy")
				}
				return strings.Join(lines, "\r\n")
			}

			// Handle "bases all" command - show all bases
			if showAll && !showEnemy && !showSummary && !showClosest && !hasCoords {
				listArgs := []string{"bases", "summary"}
				return i.gowarsCommands["list"].Handler(listArgs, conn)
			}

			// Default: show friendly bases
			listArgs := []string{"friendly", "bases", "summary"}
			return i.gowarsCommands["list"].Handler(listArgs, conn)
		},
		Help: "List various BASE information\r\n" +
			"Syntax: BAses [<keywords>]\r\n" +
			"\r\n" +
			"List location and shield percent of friendly bases; location of known\r\n" +
			"enemy bases; or count of bases of either side within a specified\r\n" +
			"range or the entire galaxy. The default range is the entire galaxy,\r\n" +
			"and the default side is friendly bases only. See the help for LIST\r\n" +
			"for more information and the complete set of keywords that can be used\r\n" +
			"to modify BASES output.\r\n" +
			"\r\n" +
			"Examples:\r\n" +
			"BA                      List location and shield percent of all friendly\r\n" +
			"                        bases.\r\n" +
			"BA ENEMY                List location of all known enemy bases.\r\n" +
			"BA SUM                  Give summary of all friendly bases.\r\n" +
			"BA ALL SUM              Give summary of all bases.\r\n" +
			"BA CL                   List the location and shield percent of the closest\r\n" +
			"                        friendly base.\r\n" +
			"BA 34 26                List the location and shield percent of friendly base\r\n" +
			"                        at 34-26 (it doesn't have to be friendly, but you\r\n" +
			"                        can't see the shield percent of an out of range enemy\r\n" +
			"                        base).",
	}

	i.gowarsCommands["build"] = Command{
		Handler: func(args []string, conn net.Conn) string {
			// Determine mode: explicit parameter or fallback to ICdef
			mode := ""
			validParams := map[string]bool{"relative": true, "absolute": true}
			paramOffset := 0

			if len(args) > 0 {
				if resolved, ok := i.resolveParameter(strings.ToLower(args[0]), validParams); ok {
					mode = resolved
					paramOffset = 1
				}
			}

			if len(args) < paramOffset+2 {
				return "Error: build command requires <vpos> <hpos> parameters. Usage: build [relative|absolute] <vpos> <hpos>"
			}

			vposStr := args[paramOffset]
			hposStr := args[paramOffset+1]
			var vpos, hpos int
			var err1, err2 error
			var galaxy uint16

			// If mode is not explicitly set, use ICdef to decide how to interpret <vpos> <hpos>
			if mode == "" {
				info, ok := i.connections.Load(conn)
				if !ok {
					return "Error: connection not found"
				}
				connInfo := info.(ConnectionInfo)
				mode = connInfo.ICdef
			}

			if mode == "relative" {
				shipX, shipY, ok := i.getShipLocation(conn)
				if !ok {
					return "Error: unable to determine planet location for relative coordinates"
				}
				vpos, err1 = strconv.Atoi(vposStr)
				hpos, err2 = strconv.Atoi(hposStr)
				if err1 != nil || err2 != nil {
					return "Error: <vpos> and <hpos> must be integers."
				}
				vpos = shipX + vpos
				hpos = shipY + hpos
			} else if mode == "absolute" {
				vpos, err1 = strconv.Atoi(vposStr)
				hpos, err2 = strconv.Atoi(hposStr)
				if err1 != nil || err2 != nil {
					return "Error: <vpos> and <hpos> must be integers."
				}
			} else {
				return "Error: Invalid mode for build command."
			}

			// Find myShip object for this connection
			info, ok := i.connections.Load(conn)
			if !ok {
				return "Error: connection not found"
			}
			connInfo := info.(ConnectionInfo)
			var myShip *Object
			var msg string

			if connInfo.Ship != nil {
				myShip = connInfo.Ship
				galaxy = connInfo.Galaxy
			}

			if myShip == nil {

				return "Error: unable to determine your ship."
			}

			// Is it adjacent?
			if (AbsInt(vpos-myShip.LocationX) > 1) || (AbsInt(hpos-myShip.LocationY) > 1) {

				return fmt.Sprintf("%s not adjacent to build location.", connInfo.Shipname)
			}

			// Build logic
			obj := i.getObjectAtLocation(myShip.Galaxy, vpos, hpos)
			if obj == nil {

				return "No object found at location"
			}

			if obj.Type != "Planet" {
				return "Not a planet"
			}

			if obj.Side != myShip.Side {
				return "Planet not yet captured."
			}

			// Do a delay
			var dlypse int
			dlypse = calculateDlypse(300, 1, 1, 6, 6)
			i.delayPause(conn, dlypse, galaxy, connInfo.Ship.Type, connInfo.Ship.Side)

			var basecnt int
			if obj.Builds <= 3 {
				obj.Builds = obj.Builds + 1
				msg = fmt.Sprintf("%d build", obj.Builds)
			} else { // must be building into base
				bases := i.getObjectsByType(connInfo.Galaxy, "Base")
				if bases != nil {
					for _, tobj := range bases {
						if tobj.Side == myShip.Side {
							basecnt = basecnt + 1
						}
					}
				}
				if basecnt == MaxBasesPerSide {
					msg = fmt.Sprintf("All Fed Bases still functional, captain.")
				} else {
					obj.Type = "Base"
					obj.Name = "Base"
					msg = fmt.Sprintf("%s builds planet into base!", connInfo.Shipname)
				}
			}
			return msg
		},
		Help: "BUILD fortifications on a captured planet\r\n" +
			"Syntax: BUild [Absolute|Relative] <vpos> <hpos>\r\n" +
			"\r\n" +
			"A fortified planet hits harder and is more resistant to destruction by\r\n" +
			"the enemy. A planet can normally be built up to 4 times. As your\r\n" +
			"team's starbases are destroyed by enemy action, a fifth build will\r\n" +
			"complete the construction of a new starbase on the planet. Only 10\r\n" +
			"starbases can be functional at any one time.\r\n" +
			"\r\n" +
			"Examples:\r\n" +
			"BU 32 12               Build the planet at sector 32-12.\r\n" +
			"BU A 32 12             Equivalent to \"BU 32 12\"\r\n" +
			"BU R 1 1               Build the planet at sector 32-12, if your present\r\n" +
			"                        location is 31-11.",
	}

	i.gowarsCommands["points"] = Command{
		Handler: func(args []string, conn net.Conn) string {
			return "Points command stub"
		},
		Help: "To be implemented",
	}

	i.gowarsCommands["capture"] = Command{
		Handler: func(args []string, conn net.Conn) string {
			var galaxy uint16
			// Determine mode: explicit parameter or fallback to ICdef
			mode := ""
			validParams := map[string]bool{"relative": true, "absolute": true}
			paramOffset := 0

			if len(args) > 0 {
				if resolved, ok := i.resolveParameter(strings.ToLower(args[0]), validParams); ok {
					mode = resolved
					paramOffset = 1
				}
			}

			if len(args) < paramOffset+2 {
				return "Error: capture command requires <vpos> <hpos> parameters. Usage: capture [relative|absolute] <vpos> <hpos>"
			}

			vposStr := args[paramOffset]
			hposStr := args[paramOffset+1]
			var vpos, hpos int
			var err1, err2 error

			// If mode is not explicitly set, use ICdef to decide how to interpret <vpos> <hpos>
			if mode == "" {
				info, ok := i.connections.Load(conn)
				if !ok {
					return "Error: connection not found"
				}
				connInfo := info.(ConnectionInfo)
				mode = connInfo.ICdef
				galaxy = connInfo.Galaxy
			}

			if mode == "relative" {
				shipX, shipY, ok := i.getShipLocation(conn)
				if !ok {
					return "Error: unable to determine ship location for relative coordinates"
				}
				vpos, err1 = strconv.Atoi(vposStr)
				hpos, err2 = strconv.Atoi(hposStr)
				if err1 != nil || err2 != nil {
					return "Error: <vpos> and <hpos> must be integers."
				}
				vpos = shipX + vpos
				hpos = shipY + hpos
			} else if mode == "absolute" {
				vpos, err1 = strconv.Atoi(vposStr)
				hpos, err2 = strconv.Atoi(hposStr)
				if err1 != nil || err2 != nil {
					return "Error: <vpos> and <hpos> must be integers."
				}
			} else {
				return "Error: Invalid mode for capture command."
			}

			// Find myShip object for this connection
			info, ok := i.connections.Load(conn)
			if !ok {
				return "Error: connection not found"
			}
			connInfo := info.(ConnectionInfo)
			var myShip *Object
			//	var idx int
			var myShipIdx int
			var capplanetnIdx int
			// Restore old logic: find myShip by name and galaxy
			for idx := range i.objects {
				obj := i.objects[idx]
				if obj.Type == "Ship" && obj.Name == connInfo.Shipname && obj.Galaxy == connInfo.Galaxy {
					myShip = obj
					myShipIdx = idx
					break
				}
			}

			if myShip == nil {
				return "Error: unable to determine your ship."
			}

			// Is it adjacent?
			if (AbsInt(vpos-myShip.LocationX) > 1) || (AbsInt(hpos-myShip.LocationY) > 1) {
				return fmt.Sprintf("%s not adjacent to planet.", connInfo.Shipname)
			}

			// Do a delay
			var dlypse int
			dlypse = calculateDlypse(300, 1, 1, 6, 6)
			i.delayPause(conn, dlypse, galaxy, connInfo.Ship.Type, connInfo.Ship.Side)

			var capplanet *Object
			var objectfound bool

			// In transaction to update the objects
			// Restore old logic: find object by iterating through all objects
			objectfound = false
			for idx := range i.objects {
				if i.objects[idx].LocationX == vpos && i.objects[idx].LocationY == hpos && i.objects[idx].Galaxy == connInfo.Galaxy {
					capplanet = i.objects[idx]
					capplanetnIdx = idx
					objectfound = true
					break
				}
			}

			if !objectfound {
				return "No object at those coordinates, sir."
			}

			// Type and side checks with early returns
			if objectfound && capplanet.Type != "Planet" {
				return "Capture THAT??  You have GOT to be kidding!!"
			}

			// Planet already captured check
			if objectfound && capplanet.Type == "Planet" && capplanet.Side == myShip.Side {
				return fmt.Sprintf("Captain, are you feeling well?\n\rWe are orbiting a %s planet!", myShip.Side)
			}

			// Calculate Planet Defense Strength (from decwar)
			// Note: Planet (capplanetnIdx) is attacking the ship (myShipIdx)
			evt, _ := i.DoDamage("Phaser", myShipIdx, capplanetnIdx, 2000)

			// Capturing a fortified enemy planet reduces attacker's ship energy
			// by 50 units (500 internal scale) for every build present on the planet
			if capplanet.Builds > 0 {
				myShip.ShipEnergy -= capplanet.Builds * 500
				if myShip.ShipEnergy < 0 {
					myShip.ShipEnergy = 0
				}
			}

			// Change the side to your side
			i.objects[capplanetnIdx].Side = i.objects[myShipIdx].Side

			// Broadcast the planet's defensive phaser hit to all players
			// Use BroadcastCombatEventWithInitiator since the planet is attacking the ship
			i.BroadcastCombatEventWithInitiator(evt, conn, conn)

			// After broadcasting the event, check for ship destruction
			if myShip.TotalShipDamage > CriticalShipDamage || myShip.ShipEnergy <= 0 {
				// Broadcast destruction message to all ships within range
				destructionMsg := fmt.Sprintf("%s has been destroyed!", myShip.Name)

				// Move player to pregame
				info, ok := i.connections.Load(conn)
				if ok {
					connInfo := info.(ConnectionInfo)
					// Set destruction cooldown before resetting connection info
					i.setDestructionCooldownForConn(connInfo, connInfo.Galaxy)
					connInfo.Section = "pregame"
					connInfo.Shipname = ""
					connInfo.Ship = nil
					connInfo.Galaxy = 0
					connInfo.Prompt = ""
					connInfo.BaudRate = 0
					i.connections.Store(conn, connInfo)
				}

				// Remove ship from galaxy and all indexes
				for idx := range i.objects {
					if i.objects[idx] == myShip {
						i.removeObjectFromSpatialIndex(myShip)
						i.removeObjectByIndex(idx)
						break
					}
				}

				return destructionMsg
			}

			// Output results in correct form
			return ""

		},
		Help: "CAPTURE a neutral or enemy planet\r\n" +
			"Syntax: CApture [Absolute|Relative] <vpos> <hpos>\r\n" +
			"\r\n" +
			"At the start of the game, all planets are neutral (they fire at\r\n" +
			"everyone!). Once captured by either side, they fire only at enemy\r\n" +
			"ships, and can be DOCKed at to refuel and rearm, just like a base\r\n" +
			"(except a planet can only supply half the resources that a base can).\r\n" +
			"Enemy planets can also be captured. When capturing an enemy planet, 1\r\n" +
			"second is added to the normal pause time of 5 seconds for each BUILD\r\n" +
			"present. Also, 50 units of ship energy are lost for each build.\r\n" +
			"\r\n" +
			"Examples:\r\n" +
			"CA 12 32                Capture planet at 12-32.\r\n" +
			"CA A 12 32              Equivalent to \"CA 12 32\".\r\n" +
			"CA R 1 1                Capture planet at sector 12-32, if your present\r\n" +
			"                        location is 11-31."}

	i.gowarsCommands["damages"] = Command{
		Handler: func(args []string, conn net.Conn) string {
			// Supported subsystem parameters
			params := []string{
				"Shields", "Warp Engines", "Impulse Engines", "Life Support", "Torpedo Tubes", "Phasers", "Computer", "Radio", "Tractor Beam",
			}
			// Compute shortest unique abbreviations
			abbrMap := make(map[string]string)
			for _, param := range params {
				for abbrLen := 1; abbrLen <= len(param); abbrLen++ {
					abbr := strings.ToLower(param[:abbrLen])
					count := 0
					for _, other := range params {
						if strings.HasPrefix(strings.ToLower(other), abbr) {
							count++
						}
					}
					if count == 1 {
						abbrMap[strings.ToLower(param)] = abbr
						break
					}
				}
			}
			// Determine output state
			outputState := "long"
			if info, ok := i.connections.Load(conn); ok {
				connInfo := info.(ConnectionInfo)
				outputState = connInfo.OutputState
			}
			if outputState == "medium" {
				return i.damagesMediumStub(args, conn)
			}
			if outputState == "short" {
				return i.damagesShortStub(args, conn)
			}
			// OutputState == "long"
			// Find user's ship
			var shipObj *Object
			var shipname string
			if info, ok := i.connections.Load(conn); ok {
				connInfo := info.(ConnectionInfo)
				shipname = connInfo.Shipname
				galaxy := connInfo.Galaxy
				shipObj = i.getShipByName(galaxy, shipname)
			}
			// Tab completion and parameter prompting
			if len(args) == 0 {
				// Check if all devices are functional (all damage = 0)
				if shipObj != nil {
					totalDamage := shipObj.ShieldsDamage + shipObj.WarpEnginesDamage + shipObj.ImpulseEnginesDamage +
						shipObj.LifeSupportDamage + shipObj.TorpedoTubeDamage + shipObj.PhasersDamage +
						shipObj.ComputerDamage + shipObj.RadioDamage + shipObj.TractorDamage
					if totalDamage == 0 {
						return "All devices functional."
					}
				}

				var stubs []string
				// First print header
				stubs = append(stubs, fmt.Sprintf("Damage Report for %s\r\n\r\nDevice                 Damage\r\n", shipname))

				for _, param := range params {
					if param == "Shields" && shipObj != nil {
						stubs = append(stubs, fmt.Sprintf("Deflector Shields: \t%.1f units", float64(shipObj.ShieldsDamage/100)))
					} else if param == "Warp Engines" && shipObj != nil {
						stubs = append(stubs, fmt.Sprintf("Warp Engines: \t\t%.1f units", float64(shipObj.WarpEnginesDamage/100)))
					} else if param == "Impulse Engines" && shipObj != nil {
						stubs = append(stubs, fmt.Sprintf("Impulse Engines: \t%.1f units", float64(shipObj.ImpulseEnginesDamage/100)))
					} else if param == "Life Support" && shipObj != nil {
						stubs = append(stubs, fmt.Sprintf("Life Support: \t\t%.1f units", float64(shipObj.LifeSupportDamage/100)))
					} else if param == "Torpedo Tubes" && shipObj != nil {
						stubs = append(stubs, fmt.Sprintf("Torpedo Tubes: \t\t%.1f units", float64(shipObj.TorpedoTubeDamage/100)))
					} else if param == "Phasers" && shipObj != nil {
						stubs = append(stubs, fmt.Sprintf("Phasers: \t\t%.1f units", float64(shipObj.PhasersDamage/100)))
					} else if param == "Computer" && shipObj != nil {
						stubs = append(stubs, fmt.Sprintf("Computer: \t\t%.1f units", float64(shipObj.ComputerDamage)/100))
					} else if param == "Radio" && shipObj != nil {
						stubs = append(stubs, fmt.Sprintf("Radio: \t\t\t%.1f units", float64(shipObj.RadioDamage/100)))
					} else if param == "Tractor Beam" && shipObj != nil {
						stubs = append(stubs, fmt.Sprintf("Tractor Beam: \t\t%.1f units", float64(shipObj.TractorDamage/100)))
					} else {
						stubs = append(stubs, fmt.Sprintf("%s:", param))
					}
				}
				return strings.Join(stubs, "\r\n")
			}
			if len(args) == 1 && strings.HasSuffix(args[0], "?") {
				prefix := strings.ToLower(strings.TrimSuffix(args[0], "?"))
				var matches []string
				for _, param := range params {
					abbr := abbrMap[strings.ToLower(param)]
					if strings.HasPrefix(strings.ToLower(param), prefix) || strings.HasPrefix(abbr, prefix) {
						matches = append(matches, param)
					}
				}
				if len(matches) == 0 {
					return "Error: No valid completion for damages parameter"
				}
				return "damages " + strings.Join(matches, " | ")
			}
			// Process multiple parameters in any order, reporting ambiguity or unknown parameter errors for each argument
			var stubs []string
			used := make(map[string]bool)
			for _, arg := range args {
				input := strings.ToLower(arg)
				var matches []string
				for _, param := range params {
					abbr := abbrMap[strings.ToLower(param)]
					if strings.HasPrefix(strings.ToLower(param), input) || strings.HasPrefix(abbr, input) {
						matches = append(matches, param)
					}
				}
				if len(matches) == 0 {
					stubs = append(stubs, fmt.Sprintf("Error: Unknown damages parameter '%s'.", arg))
				} else if len(matches) > 1 {
					stubs = append(stubs, fmt.Sprintf("Error: Ambiguous damages parameter '%s'. Please be more specific.", arg))
				} else if !used[matches[0]] {
					if matches[0] == "Shields" && shipObj != nil {
						stubs = append(stubs, fmt.Sprintf("Deflector Shields: \t%.1f units", float64(shipObj.ShieldsDamage/100)))
					} else if matches[0] == "Warp Engines" && shipObj != nil {
						stubs = append(stubs, fmt.Sprintf("Warp Engines: \t\t%.1f units", float64(shipObj.WarpEnginesDamage/100)))
					} else if matches[0] == "Impulse Engines" && shipObj != nil {
						stubs = append(stubs, fmt.Sprintf("Impulse Engines: \t%.1f units", float64(shipObj.ImpulseEnginesDamage/100)))
					} else if matches[0] == "Life Support" && shipObj != nil {
						stubs = append(stubs, fmt.Sprintf("Life Support: \t\t%.1f units", float64(shipObj.LifeSupportDamage/100)))
					} else if matches[0] == "Torpedo Tubes" && shipObj != nil {
						stubs = append(stubs, fmt.Sprintf("Torpedo Tubes: \t\t%.1f units", float64(shipObj.TorpedoTubeDamage/100)))
					} else if matches[0] == "Phasers" && shipObj != nil {
						stubs = append(stubs, fmt.Sprintf("Phasers: \t\t%.1f units", float64(shipObj.PhasersDamage/100)))
					} else if matches[0] == "Computer" && shipObj != nil {
						stubs = append(stubs, fmt.Sprintf("Computer: \t\t%.1f units", float64(shipObj.ComputerDamage/100)))
					} else if matches[0] == "Radio" && shipObj != nil {
						stubs = append(stubs, fmt.Sprintf("Radio: \t\t\t%.1f units", float64(shipObj.RadioDamage/100)))
					} else if matches[0] == "Tractor Beam" && shipObj != nil {
						stubs = append(stubs, fmt.Sprintf("Tractor Beam: \t\t%.1f units", float64(shipObj.TractorDamage/100)))
					} else {
						stubs = append(stubs, fmt.Sprintf("%s:", matches[0]))
					}
					used[matches[0]] = true
				}
			}
			return strings.Join(stubs, "\r\n")
		},
		Help: "DAMAGE report\r\n" +
			"Syntax: DAmages [<device names>]\r\n" +
			"\r\n" +
			"List damaged ship devices and the amount of damage to each. The\r\n" +
			"condition of all or just selected devices may be examined. Total ship\r\n" +
			"damage is not reported.\r\n" +
			"\r\n" +
			"Examples:\r\n" +
			"DA                      List all damaged devices and their current damages.\r\n" +
			"DA SH T                 List damages for SHields and Torpedo tubes.\r\n" +
			"DA PH RA C              List damages for PHasers, sub-space RAdio, and\r\n" +
			"                        Computer.",
	}

	// dock changed to dock to adjacent base/planet on your side
	// DECWAR resource scaling and device repair logic applied.
	const (
		BaseEnergyGain         = 10000
		PlanetEnergyGain       = 5000
		BaseShieldGain         = 5000
		PlanetShieldGain       = 2500
		BaseTorpedoGain        = 10
		PlanetTorpedoGain      = 5
		LifeSupportGain        = 5
		BaseDamageRepair       = 100
		BaseDamageRepairDocked = 300
		maxLifeSupport         = 100 // Set as appropriate for your game
	)
	i.gowarsCommands["dock"] = Command{
		Handler: func(args []string, conn net.Conn) string {
			var galaxy uint16

			// Accept optional parameters: <status> [warp] [impulse] [torpedos] [phasers] [shields] [computer] [lifesupport] [radio] [tractor]
			var status string
			_ = status
			var hullRepairInternal int
			var requestedDevices []string
			allowedDevices := map[string]bool{
				"warp":        true,
				"impulse":     true,
				"torpedos":    true,
				"phasers":     true,
				"shields":     true,
				"computer":    true,
				"lifesupport": true,
				"radio":       true,
				"tractor":     true,
			}
			allowedStatus := map[string]bool{"status": true}

			// List of allowed optional parameters for dock
			dockOptions := "[status] [warp] [impulse] [torpedos] [phasers] [shields] [computer] [lifesupport] [radio] [tractor]"

			// Robust parameter prompting logic: always prompt if no args, empty input, or single empty string (for abbreviations like "do")
			// If no arguments or only whitespace, proceed to dock with no options
			if len(args) == 0 || (len(args) == 1 && (strings.TrimSpace(args[0]) == "" || args[0] == "")) {
				// No status, no requested devices; just dock
				args = []string{}
			}
			if len(args) == 1 && (args[0] == "?" || strings.TrimSpace(args[0]) == "?") {
				return "Dock command optional parameters: " + dockOptions + ".\nYou may specify any combination of: status, warp, impulse, torpedos, phasers, shields, computer, lifesupport, radio, tractor."
			}
			if len(args) > 0 {
				// Try to resolve first parameter as 'status' or a device (abbreviation allowed)
				_, ok := i.resolveParameter(args[0], allowedStatus)
				isStatus := ok
				if !ok {
					ok = false
					_, ok = i.resolveParameter(args[0], allowedDevices)
				}
				if !ok {
					return "Syntax: DOck [<status>] [warp] [impulse] [torpedos] [phasers] [shields] [computer] [lifesupport] [radio] [tractor]"
				}
				if isStatus {
					status = "status"
					// Resolve subsequent device parameters (abbreviations allowed)
					if len(args) > 1 {
						for _, arg := range args[1:] {
							dev, ok := i.resolveParameter(arg, allowedDevices)
							if ok {
								requestedDevices = append(requestedDevices, dev)
							} else {
								return "Error: invalid or ambiguous device parameter '" + arg + "'. Allowed: warp, impulse, torpedos, phasers, shields, computer, lifesupport, radio, tractor."
							}
						}
					}
				} else {
					// No status, just devices
					for _, arg := range args {
						dev, ok := i.resolveParameter(arg, allowedDevices)
						if ok {
							requestedDevices = append(requestedDevices, dev)
						} else {
							return "Error: invalid or ambiguous device parameter '" + arg + "'. Allowed: warp, impulse, torpedos, phasers, shields, computer, lifesupport, radio, tractor."
						}
					}
				}
			}
			// Find myShip object for this connection
			info, ok := i.connections.Load(conn)
			if !ok {
				return "Error: connection not found"
			}
			connInfo := info.(ConnectionInfo)
			var myShip *Object

			if connInfo.Ship != nil {
				myShip = connInfo.Ship
				galaxy = connInfo.Galaxy
			}
			if myShip == nil {
				return "Error: unable to determine your ship."
			}

			// Check all adjacent sectors for a friendly base or planet
			var adjacentPort *Object
			foundAdjacent := false
			for dx := -1; dx <= 1; dx++ {
				for dy := -1; dy <= 1; dy++ {
					if dx == 0 && dy == 0 {
						continue // skip the ship's own position
					}
					nx := myShip.LocationX + dx
					ny := myShip.LocationY + dy
					// if nx < 0 || ny < 0 || nx >= MaxSizeX || ny >= MaxSizeY {
					if nx < 1 || ny < 1 || nx > MaxSizeX || ny > MaxSizeY {
						continue
					}
					obj := i.getObjectAtLocation(connInfo.Galaxy, nx, ny)
					if obj != nil && ((obj.Type == "Planet" || obj.Type == "Base") && obj.Side == myShip.Side) {
						adjacentPort = obj
						foundAdjacent = true
						break
					}
				}
				if foundAdjacent {
					break
				}
			}
			if !foundAdjacent {
				return fmt.Sprintf("%s not adjacent to planet.", connInfo.Shipname)
			}
			// Use adjacentPort as the port/base/planet to dock at
			capplanet := adjacentPort

			// Determine if docking at base or planet
			isBase := capplanet.Type == "Base"
			isPlanet := capplanet.Type == "Planet"

			// Preserve alert status if present
			wasRed := false
			if strings.Contains(myShip.Condition, "Red") {
				wasRed = true
			}

			// Check if already docked BEFORE setting new condition
			alreadyDocked := strings.Contains(strings.ToLower(myShip.Condition), "docked")

			// Set Condition to docked, preserving alert if needed
			if wasRed {
				myShip.Condition = "Docked+Red"
			} else {
				myShip.Condition = "Docked"
			}

			// --- DECWAR Resource Scaling and resource replenishment---
			// Energy
			if isBase {
				if myShip.ShipEnergy+BaseEnergyGain > InitialShipEnergy {
					myShip.ShipEnergy = InitialShipEnergy
				} else {
					myShip.ShipEnergy += BaseEnergyGain
				}
			} else if isPlanet {
				if myShip.ShipEnergy+PlanetEnergyGain > InitialShipEnergy {
					myShip.ShipEnergy = InitialShipEnergy
				} else {
					myShip.ShipEnergy += PlanetEnergyGain
				}
			}

			// Torpedoes (bases max out torps, planets go up 5)
			maxTorpedoes := BaseTorpedoGain
			if isBase {
				myShip.TorpedoTubes = BaseTorpedoGain
			} else if isPlanet {
				if myShip.TorpedoTubes+PlanetTorpedoGain > maxTorpedoes {
					myShip.TorpedoTubes = maxTorpedoes
				} else {
					myShip.TorpedoTubes += PlanetTorpedoGain
				}
			}

			// Shields
			if isBase {
				if myShip.Shields+BaseShieldGain > InitialShieldValue {
					myShip.Shields = InitialShieldValue
				} else {
					myShip.Shields += BaseShieldGain
				}
			} else if isPlanet {
				if myShip.Shields+PlanetShieldGain > InitialShieldValue {
					myShip.Shields = InitialShieldValue
				} else {
					myShip.Shields += PlanetShieldGain
				}
			}

			// Life Support
			if myShip.LifeSupportReserve+LifeSupportGain > maxLifeSupport {
				myShip.LifeSupportReserve = maxLifeSupport
			} else {
				myShip.LifeSupportReserve += LifeSupportGain
			}

			// --- Hull Repair on Dock  ---
			// Determine hull repair amount
			// Hull damage is stored at 100x scale (see comments elsewhere)
			if isBase {
				if alreadyDocked {
					hullRepairInternal = 20000
				} else {
					hullRepairInternal = 10000
				}
			} else if isPlanet {
				if alreadyDocked {
					hullRepairInternal = 10000
				} else {
					hullRepairInternal = 5000
				}
			}
			if myShip.TotalShipDamage > hullRepairInternal {
				myShip.TotalShipDamage -= hullRepairInternal
			} else {
				myShip.TotalShipDamage = 0
			}

			// --- Device Damage Repair on Dock (DECWAR logic) ---
			// Device repair amount per table
			deviceRepair := 0
			if isBase {
				if alreadyDocked {
					deviceRepair = 30
				} else {
					deviceRepair = 30
				}
			} else if isPlanet {
				if alreadyDocked {
					deviceRepair = 30
				} else {
					deviceRepair = 30
				}
			}

			// Device damage is stored at 100x scale with display
			// Repair all devices (damage cannot go below zero)
			deviceRepairInternal := deviceRepair * 100
			if deviceRepairInternal > 0 {
				if myShip.WarpEnginesDamage > 0 {
					if myShip.WarpEnginesDamage > deviceRepairInternal {
						myShip.WarpEnginesDamage -= deviceRepairInternal
					} else {
						myShip.WarpEnginesDamage = 0
					}
				}
				if myShip.ImpulseEnginesDamage > 0 {
					if myShip.ImpulseEnginesDamage > deviceRepairInternal {
						myShip.ImpulseEnginesDamage -= deviceRepairInternal
					} else {
						myShip.ImpulseEnginesDamage = 0
					}
				}
				if myShip.TorpedoTubeDamage > 0 {
					if myShip.TorpedoTubeDamage > deviceRepairInternal {
						myShip.TorpedoTubeDamage -= deviceRepairInternal
					} else {
						myShip.TorpedoTubeDamage = 0
					}
				}
				if myShip.PhasersDamage > 0 {
					if myShip.PhasersDamage > deviceRepairInternal {
						myShip.PhasersDamage -= deviceRepairInternal
					} else {
						myShip.PhasersDamage = 0
					}
				}
				if myShip.ShieldsDamage > 0 {
					if myShip.ShieldsDamage > deviceRepairInternal {
						myShip.ShieldsDamage -= deviceRepairInternal
					} else {
						myShip.ShieldsDamage = 0
					}
				}
				if myShip.ComputerDamage > 0 {
					if myShip.ComputerDamage > deviceRepairInternal {
						myShip.ComputerDamage -= deviceRepairInternal
					} else {
						myShip.ComputerDamage = 0
					}
				}
				if myShip.LifeSupportDamage > 0 {
					if myShip.LifeSupportDamage > deviceRepairInternal {
						myShip.LifeSupportDamage -= deviceRepairInternal
					} else {
						myShip.LifeSupportDamage = 0
					}
				}
				if myShip.RadioDamage > 0 {
					if myShip.RadioDamage > deviceRepairInternal {
						myShip.RadioDamage -= deviceRepairInternal
					} else {
						myShip.RadioDamage = 0
					}
				}
				if myShip.TractorDamage > 0 {
					if myShip.TractorDamage > deviceRepairInternal {
						myShip.TractorDamage -= deviceRepairInternal
					} else {
						myShip.TractorDamage = 0
					}
				}
			}

			// Process 'status' if requested
			if status == "status" {
				i.processDockStatus(conn, myShip)
			}

			// Do a delay
			var dlypse int
			dlypse = calculateDlypse(300, 1, 1, 6, 6)
			i.delayPause(conn, dlypse, galaxy, connInfo.Ship.Type, connInfo.Ship.Side)

			// Ensure all connections see the updated ship state
			i.refreshShipPointers()
			return "DOCKED."
		},
		Help: "DOCK at a friendly base or planet\r\n" +
			"Syntax: DOck [<status>] [warp] [impulse] [torpedos] [phasers] [shields] [computer] [lifesupport] [radio] [tractor]\r\n" +
			"\r\n" +
			"Refuel, rearm, repair your ship's hull, and repair all ship devices per DECWAR rules. Your ship's condition is set to docked.\r\n" +
			"While docked, you gain resources, hull repair, and device repair per the following:\r\n" +
			"Base: +1000 energy, +500 shields, +10 torpedoes, +5 life support, -100 hull damage (or -200 if already docked), -10 device damage (or -20 if already docked)\r\n" +
			"Planet: +500 energy, +250 shields, +5 torpedoes, +5 life support, -50 hull damage (or -100 if already docked), -5 device damage (or -10 if already docked)\r\n" +
			"Device damage is automatically repaired by docking, per the above table. Use the REPAIR command for additional device repair.\r\n" +
			"If you have no damages and are completely refueled and rearmed, DOCKing will have no effect on your ship. A\r\n" +
			"STATUS command string can be appended to a DOCK order as the first parameter.\r\n" +
			"You may also specify any combination of the following device names to request status or action on them after docking:\r\n" +
			"warp, impulse, torpedos, phasers, shields, computer, lifesupport, radio, tractor.\r\n" +
			"\r\n" +
			"Examples:\r\n" +
			"DO                      Dock, no status report.\r\n" +
			"DO ST                   Dock, show ship's status AFTER docking.\r\n" +
			"DO ST shields phasers   Dock, show ship's status and shields and phasers AFTER docking.",
	}

	// Handler for: energy <shipname> <units>
	// Prompts for shipname if missing, supports abbreviation and completion
	i.gowarsCommands["energy"] = Command{
		Handler: func(args []string, conn net.Conn) string {

			info, ok := i.connections.Load(conn)
			if !ok || info.(ConnectionInfo).Section != "gowars" || info.(ConnectionInfo).Shipname == "" {
				return "You must be in GOWARS with a ship to use this command"
			}
			connInfo := info.(ConnectionInfo)

			// Prompt for shipname if not provided
			if len(args) == 0 {
				// List available ships in this galaxy
				var lines []string
				for _, obj := range i.objects {
					if obj.Type == "Ship" && obj.Galaxy == connInfo.Galaxy {
						lines = append(lines, fmt.Sprintf("energy %s <units>", obj.Name))
					}
				}
				if len(lines) == 0 {
					return "No ships found in this galaxy."
				}
				return "Specify a shipname:\r\n" + strings.Join(lines, "\r\n")
			}

			// Expand abbreviated ship name (like tell)
			param := strings.ToLower(args[0])
			var matches []string
			for _, obj := range i.objects {
				if obj.Type == "Ship" && obj.Galaxy == connInfo.Galaxy && strings.HasPrefix(strings.ToLower(obj.Name), param) {
					matches = append(matches, obj.Name)
				}
			}

			if len(matches) == 0 {
				return "Error: no ship matches abbreviation"
			} else if len(matches) > 1 {
				return "Error: ambiguous ship abbreviation, matches: " + strings.Join(matches, ", ")
			}

			shipname := matches[0]
			// Parse units parameter (optional, but required for this stub)
			if len(args) < 2 {
				return "Error: you must specify <units> of energy to transfer (e.g., energy ship1 1000)"
			}
			unitsStr := args[1]
			units, err := strconv.Atoi(unitsStr)
			if err != nil {
				return "Error: units must be an integer"
			}

			// Find my ship and the target ship
			myShip := ""
			myX, myY := -1, -1
			targetX, targetY := -1, -1
			for _, obj := range i.objects {
				if obj.Type == "Ship" && obj.Galaxy == connInfo.Galaxy {
					if obj.Name == connInfo.Shipname {
						myShip = obj.Name
						myX = obj.LocationX
						myY = obj.LocationY
					}
					if obj.Name == shipname {
						targetX = obj.LocationX
						targetY = obj.LocationY
					}
				}
			}

			if shipname == myShip {
				return "Transfer energy to US!?!"
			}

			// Check adjacency (orthogonal or diagonal)
			adjacent := false
			if myX != -1 && myY != -1 && targetX != -1 && targetY != -1 {
				dx := AbsInt(myX - targetX)
				dy := AbsInt(myY - targetY)
				if (dx <= 1 && dy <= 1) && !(dx == 0 && dy == 0) {
					adjacent = true
				}
			}
			if !adjacent {
				return "Not adjacent to destination ship"
			}

			// 10% of  the energy  transferred will be lost due to broadcast dissipation
			// Sending ship looses 100%, receiving ship gets 90%
			// If you attempt to send more energy than the other ship  can  store  (ie  5000 units),
			// the  transfer  will  automatically  be reduced to the maximum possible.

			const maxShipEnergy = 5000

			var myShipObj, targetShipObj *Object
			myShipObj = i.getShipByName(connInfo.Galaxy, myShip)
			targetShipObj = i.getShipByName(connInfo.Galaxy, shipname)

			if myShipObj == nil || targetShipObj == nil {
				return "Error: could not find one or both ships"
			}

			if units <= 0 {
				return "Illegal energy transfer.  Transfer aborted."
			}
			if myShipObj.ShipEnergy < units {
				return "Error: not enough energy to transfer"
			}

			// Calculate max energy that can be received (in decwar format)
			energyToGive := units * 10
			energyToReceive := int(float64(units)*0.9) * 10
			spaceLeft := (maxShipEnergy * 10) - targetShipObj.ShipEnergy

			if energyToReceive > spaceLeft {
				energyToReceive = spaceLeft
				energyToGive = int(float64(energyToReceive) / 0.9)
				if float64(energyToGive)*0.9 < float64(energyToReceive) {
					energyToGive++ // round up if needed
				}
			}
			if energyToGive > myShipObj.ShipEnergy {
				energyToGive = myShipObj.ShipEnergy
				energyToReceive = int(float64(energyToGive) * 0.9)
			}

			if energyToGive <= 0 || energyToReceive <= 0 {
				return "No energy transferred."
			}

			myShipObj.ShipEnergy -= energyToGive
			targetShipObj.ShipEnergy += energyToReceive
			if targetShipObj.ShipEnergy > maxShipEnergy*10 {
				targetShipObj.ShipEnergy = maxShipEnergy
			}

			// Output message to receiving ship
			i.connections.Range(func(key, value interface{}) bool {
				otherConn := key.(net.Conn)
				otherConnInfo := value.(ConnectionInfo)
				if otherConnInfo.Shipname == targetShipObj.Name && otherConnInfo.Galaxy == targetShipObj.Galaxy {
					if writerRaw, ok := i.writers.Load(otherConn); ok {
						writer := writerRaw.(*bufio.Writer)
						i.writeBaudf(otherConn, writer, "%s transfers %d units of energy to the %s\r\n", myShipObj.Name, energyToReceive/10, targetShipObj.Name)
						prompt := i.getPrompt(otherConn)
						if mutexRaw, ok := i.writerMutexs.Load(otherConn); ok {
							mutex := mutexRaw.(*sync.Mutex)
							mutex.Lock()
							writer.WriteString(prompt)
							writer.Flush()
							mutex.Unlock()
						}
					}
					return false // Only send to the first matching connection
				}
				return true
			})

			return "Energy transferred, Captain."
		},
		Help: "Transfer ENERGY to a friendly ship\r\n" +
			"Syntax: Energy <ship name> <units of energy to transfer>\r\n" +
			"\r\n" +
			"The receiving ship must be located in an adjacent sector. 10% of the\r\n" +
			"energy transferred will be lost due to broadcast dissipation. If you\r\n" +
			"attempt to send more energy than the other ship can store (ie 5000\r\n" +
			"units), the transfer will automatically be reduced to the maximum\r\n" +
			"possible.\r\n" +
			"\r\n" +
			"Example:\r\n" +
			"E I 1000                Transfer 1000 units of energy to the Intrepid. The\r\n" +
			"                        Intrepid will receive 900 units of energy."}

	i.gowarsCommands["gripe"] = Command{
		Handler: func(args []string, conn net.Conn) string {
			if len(args) == 0 {
				data, err := os.ReadFile("gripe.txt")
				if err != nil {
					return fmt.Sprintf("Error reading gripe.txt: %v", err)
				}
				lines := strings.Split(string(data), "\n")
				for idx, line := range lines {
					lines[idx] = strings.TrimRight(line, "\r")
				}
				return strings.Join(lines, "\r\n")
			}

			// Sanitize gripe text
			gripeText := sanitizeGripeText(strings.Join(args, " "))
			if gripeText == "" {
				return "Error: gripe text cannot be empty or contain only control characters"
			}

			// Get connection info for IP logging
			var sourceIP string
			if info, ok := i.connections.Load(conn); ok {
				connInfo := info.(ConnectionInfo)
				sourceIP = connInfo.IP
			} else {
				// Fallback to getting IP from connection
				if addr := conn.RemoteAddr(); addr != nil {
					sourceIP, _, _ = net.SplitHostPort(addr.String())
				}
			}

			// Rotate gripe file if needed
			if err := rotateGripeFile("gripe.txt"); err != nil {
				log.Printf("Error rotating gripe file: %v", err)
			}

			file, err := os.OpenFile("gripe.txt", os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0644)
			if err != nil {
				return fmt.Sprintf("Error writing to gripe.txt: %v", err)
			}
			defer file.Close()

			// Write gripe with timestamp and source IP
			timestamp := time.Now().Format(time.RFC3339)
			if _, err := fmt.Fprintf(file, "[%s] [%s] %s\n", timestamp, sourceIP, gripeText); err != nil {
				return fmt.Sprintf("Error writing to gripe.txt: %v", err)
			}

			return fmt.Sprintf("Gripe recorded: %s", gripeText)
		},
		Help: "Submit a GRIPE\r\n" +
			"Syntax: Gripe\r\n" +
			"\r\n" +
			"Add a comment, bug report, suggestion, etc. to the top of file\r\n" +
			"gripe.txt. Type in your comments, then enter to exit and\r\n" +
			"continue the game.\r\n" +
			"Each gripe is preceded with a header that includes the version number,\r\n" +
			"date, time, ship name, user name, TTY speed and game options.\r\n" +
			"To view gripes not yet acted upon, type the file gripe.txt. ",
	}

	//Impulse command logic here - hsn
	i.gowarsCommands["impulse"] = Command{
		Handler: func(args []string, conn net.Conn) string {
			var msg string
			var galaxy uint16
			info, ok := i.connections.Load(conn)
			if !ok || info.(ConnectionInfo).Section != "gowars" || info.(ConnectionInfo).Shipname == "" {
				return "You must be in GOWARS with a ship to use this command"
			}
			connInfo := info.(ConnectionInfo)

			// Prompting for shipnames when "impulse computed ?" is entered
			if len(args) == 2 && args[0] == "computed" && args[1] == "?" {
				// Check if attacker's computer has more than CriticalDamage
				info, ok := i.connections.Load(conn)
				if ok {
					connInfo := info.(ConnectionInfo)
					for idx := range i.objects {
						obj := i.objects[idx]
						if obj.Type == "Ship" && obj.Name == connInfo.Shipname && obj.Galaxy == connInfo.Galaxy {
							if obj.ComputerDamage > CriticalDamage {
								return "Computer inoperative."
							}
							break
						}
					}

				}

				info, ok = i.connections.Load(conn)
				if !ok {
					return "Connection info not found"
				}
				galaxy := info.(ConnectionInfo).Galaxy
				var lines []string
				for _, obj := range i.objects {
					if obj.Type == "Ship" && obj.Galaxy == galaxy {
						lines = append(lines, fmt.Sprintf("move computed %s", obj.Name))
					}
				}
				if len(lines) == 0 {
					return "No ships found in this galaxy."
				}
				return strings.Join(lines, "\r\n")
			}

			// Supported options
			options := map[string]bool{"absolute": true, "relative": true, "computed": true}
			moveParams := []string{"absolute", "relative", "computed"}
			// Expand abbreviations in args before parsing (expand as far as unique)
			for i := range args {
				argLower := strings.ToLower(args[i])
				matches := []string{}
				for _, param := range moveParams {
					if strings.HasPrefix(param, argLower) {
						matches = append(matches, param)
					}
				}
				if len(matches) == 1 {
					args[i] = matches[0]
				}
			}

			params := []string{}
			xArg, yArg := "", ""

			// Parse up to 4 options
			for len(args) > 0 && options[strings.ToLower(args[0])] && len(params) < 4 {
				params = append(params, strings.ToLower(args[0]))
				args = args[1:]
			}

			// Set default mode (from set Icdef)
			mode := connInfo.ICdef

			// Parse coordinates - is the first arg a word?
			if len(params) > 0 {
				if params[0] == "absolute" || params[0] == "relative" || params[0] == "computed" {
					mode = params[0] //set move mode to requested mode
				}
			}
			if mode == "absolute" || mode == "relative" {
				if len(args) > 0 {
					xArg = args[0]
				}
				if len(args) > 1 {
					yArg = args[1]
				}
			} else if mode == "computed" {
				if len(args) > 0 {
					// Check if attacker's computer has more than CriticalDamage
					info, ok := i.connections.Load(conn)
					if ok {
						connInfo := info.(ConnectionInfo)

						for idx := range i.objects {
							obj := i.objects[idx]
							if obj.Type == "Ship" && obj.Name == connInfo.Shipname && obj.Galaxy == connInfo.Galaxy {
								if obj.ComputerDamage > CriticalDamage {

									return "Computer inoperative."
								}
								break
							}
						}

					}

					// Support multi-word/prefix shipname abbreviation (e.g., 'mo c e')
					info, _ = i.connections.Load(conn)
					var allShipNames []string
					for _, obj := range i.objects {
						if obj.Type == "Ship" && obj.Galaxy == info.(ConnectionInfo).Galaxy {
							allShipNames = append(allShipNames, obj.Name)
						}
					}
					abbrParts := args
					var matchedShips []string
					for _, name := range allShipNames {
						match := true
						searchIdx := 0
						for _, part := range abbrParts {
							partLower := strings.ToLower(part)
							idx := strings.Index(strings.ToLower(name[searchIdx:]), partLower)
							if idx == -1 {
								match = false
								break
							}
							searchIdx += idx + len(partLower)
						}
						if match {
							matchedShips = append(matchedShips, name)
						}
					}
					if len(matchedShips) == 1 {
						computedShip := matchedShips[0]
						for _, obj := range i.objects {
							if obj.Type == "Ship" && obj.Galaxy == info.(ConnectionInfo).Galaxy && obj.Name == computedShip {
								xArg = strconv.Itoa(obj.LocationX)
								yArg = strconv.Itoa(obj.LocationY)
							}
						}
					} else if len(matchedShips) == 0 {
						return "<shipname> not found"
					} else {
						return "Ambiguous shipname abbreviation"
					}
				} else {
					return fmt.Sprintf("<shipname> is required")
				}
			}

			// Prompt for missing values
			if mode == "computed" {
				if xArg == "" {
					return fmt.Sprintf("<shipname> is required")
				}
			} else {
				if mode == "absolute" || mode == "relative" {
					if xArg == "" || yArg == "" {
						return "<vpos> <hpos> are required"
					}
				}
			}

			var targetX int
			var targetY int
			var err error
			// Parse coordinates if absolute or relative
			if mode == "absolute" || mode == "relative" {
				targetX, targetY, err = i.parseCoordinates(xArg, yArg, conn, false)
				if err != nil {
					return err.Error()
				}
			}

			targetX, _ = strconv.Atoi(xArg)
			targetY, _ = strconv.Atoi(yArg)
			// If computed, apply custom logic (example: average of current and target)
			if mode == "computed" {
				_, _, ok := i.getShipLocation(conn)
				if !ok {
					return "Cannot find ship location"
				}
			} else {
				if mode == "relative" {
					startX, startY, ok := i.getShipLocation(conn)

					if !ok {
						return "Cannot find ship location"
					}
					targetX = startX + targetX
					targetY = startY + targetY
				}
			}

			// Validate boundaries
			if targetX < BoardStart || targetX > MaxSizeX {
				return fmt.Sprintf("X coordinate lies outside galaxy.")
			}
			if targetY < BoardStart || targetY > MaxSizeY {
				return fmt.Sprintf("Y coordinate lies outside galaxy.")
			}

			// Get current ship location
			startX, startY, ok := i.getShipLocation(conn)
			if !ok {
				return "Cannot find ship location"
			}

			// Check if already at target
			if startX == targetX && startY == targetY {
				return fmt.Sprintf("Already at (%d, %d)", targetX, targetY)
			}

			// Check condition for my ships engine damage and limit move it necessary
			if info, ok := i.connections.Load(conn); ok {
				connInfo := info.(ConnectionInfo)
				shipname := connInfo.Shipname
				galaxy := connInfo.Galaxy

				for idx := range i.objects {
					obj := i.objects[idx]
					if obj.Type == "Ship" && obj.Name == shipname && obj.Galaxy == galaxy {
						if obj.ImpulseEnginesDamage > 0 && obj.ImpulseEnginesDamage < 300 {
							//If engines damaged, Check if within max impulse range (1)
							if max(AbsInt(startX-targetX), (AbsInt(startY-targetY))) > 1 {
								if connInfo.OutputState == "long" {

									return "Captain, the impulse engines won't take it.  Maximum speed warp 1."
								} else {

									return "Maximum speed warp 1."
								}
							}
						} else {
							//Check if engine damage > 300 (the  device is inoperative.)
							if obj.ImpulseEnginesDamage >= 300 {

								return "Impulse engines damaged."
							}

							//Check if within max impulse range (1)
							if (AbsInt(startX-targetX) > 1) || (AbsInt(startY-targetY) > 1) {
								if connInfo.OutputState == "long" {

									return "Captain, the impulse engines won't take it.  Maximum speed warp 1."
								} else {

									return "Maximum speed warp 1."
								}
							}
						}

						//Energy  consumption:
						//The base energy cost is computed as 40 * ia * ia, meaning the energy cost is proportional to the square of the maximum distance moved.
						warpFactor := max(AbsInt(startX-targetX), (AbsInt(startY - targetY)))
						cost := CostFactor * warpFactor * warpFactor

						// If a ship's shields are up, the amount  of energy expended during movement is doubled.
						if obj.ShieldsUpDown == true {
							cost = cost * 2
						}

						obj.ShipEnergy = obj.ShipEnergy - cost
						break
					}
				}

			}

			var d float32
			d = 0
			if info, ok := i.connections.Load(conn); ok {
				connInfo := info.(ConnectionInfo)
				shipname := connInfo.Shipname
				galaxy := connInfo.Galaxy
				if obj := i.getShipByName(galaxy, shipname); obj != nil {
					if obj.ComputerDamage > CriticalDamage {
						i.galaxiesMutex.RLock()
						impGal := i.galaxies[galaxy]
						i.galaxiesMutex.RUnlock()
						impRng := newSeededRand()
						if impGal != nil {
							impRng = impGal.rng
						}
						d = (float32(impRng.Float64()) * .5) - 0.25 //Just like decwar
					}
				}
			}

			// Compute the distance
			dist := max(AbsInt(startX-targetX), (AbsInt(startY - targetY)))

			// Get the path cells
			pathCells, targetX, targetY := getPathCells(startX, startY, targetX, targetY, dist, d)
			// Build map of occupied cells, excluding the player's ship
			occupiedCells := make(map[[2]int]bool)
			for _, obj := range i.objects {
				if obj.Galaxy == connInfo.Galaxy && (obj.Type != "Ship" || obj.Name != connInfo.Shipname) {
					occupiedCells[[2]int{obj.LocationX, obj.LocationY}] = true
				}
			}

			// Check for collisions along the path (excluding start position)
			// Track last safe cell before collision
			lastSafeCell := [2]int{startX, startY}
			collisionDetected := false

			for _, cell := range pathCells[:1] {
				if occupiedCells[cell] {
					collisionDetected = true
					break
				}
				lastSafeCell = cell
			}

			// Update ship position & condition
			for idx, obj := range i.objects {
				if obj.Type == "Ship" && obj.Name == connInfo.Shipname && obj.Galaxy == connInfo.Galaxy {
					// Validate galaxy boundaries before moving
					finalX, finalY := targetX, targetY
					if !collisionDetected {
						isValid, maxX, maxY := i.validateGalaxyBoundaries(connInfo.Galaxy, targetX, targetY)
						if !isValid {
							msg += fmt.Sprintf("Navigation Officer: \"Captain, those coordinates (%d, %d) are outside the galaxy boundaries (1,1 to %d,%d)!\"\n\r",
								targetX, targetY, maxX, maxY)
							finalX, finalY = lastSafeCell[0], lastSafeCell[1]
							collisionDetected = true
						}
					}

					if collisionDetected {
						i.updateObjectLocation(i.objects[idx], lastSafeCell[0], lastSafeCell[1])
						i.objects[idx].Condition = "Green"
					} else {
						i.updateObjectLocation(i.objects[idx], finalX, finalY)
						i.objects[idx].Condition = "Green"
					}
					break
				}
			}

			shipToMove := connInfo.Ship
			// Tractor logic: move tractored ship if tractor is on (call while holding lock to avoid race)
			i.moveTractoredShipIfNeededNoLock(shipToMove, startX, startY, targetX, targetY, pathCells)

			// Update galaxy tracker
			i.trackerMutex.Lock()
			if tracker, exists := i.galaxyTracker[connInfo.Galaxy]; exists {
				tracker.LastActive = time.Now()
				i.galaxyTracker[connInfo.Galaxy] = tracker
			} else {
				now := time.Now()
				i.galaxyTracker[connInfo.Galaxy] = GalaxyTracker{GalaxyStart: now, LastActive: now}
			}
			i.trackerMutex.Unlock()

			if collisionDetected {
				msg = msg + fmt.Sprintf("Navigation Officer:  \"Collision averted, Captain!\"\n\r")
			}
			//
			// Perform delay calc and pause for move
			// Calc pause based on slwest (from decwar):
			//	slwest = 3 (<=1200)
			//	slwest = 2 (=1200?)
			//	slwest = 1 (>1200)
			//	slwest = 1 (= 0)
			// decwar: Simple move charge: (slwest×1000)+1000
			//         if going > 4 sectors: rand(4000)/30 (add or not?)
			var dlypse int
			if info, ok := i.connections.Load(conn); ok {
				dlypse = calculateDlypse(info.(ConnectionInfo).BaudRate, startX, startY, targetX, targetY)
			}

			destructionMsg := i.delayPause(conn, dlypse, galaxy, connInfo.Ship.Type, connInfo.Ship.Side)
			return msg + destructionMsg
		},
		Help: "IMPULSE\r\n" +
			"Move using IMPULSE engines\r\n" +
			"Syntax: Impulse [Absolute|Relative] <vpos> <hpos>\r\n" +
			"\r\n" +
			"Move one sector vertically, horizontally, or diagonally (equivalent to\r\n" +
			"warp factor 1). Ship condition changes to green.\r\n" +
			"\r\n" +
			"Examples:\r\n" +
			"I 37 45                Move to sector 37-45.\r\n" +
			"I A 37 45              Equivalent to \"I 37 45\".\r\n" +
			"I R 1 -1               Move to sector 37-45, if your ship's present location\r\n" +
			"                        is 36-46.",
	}

	i.gowarsCommands["news"] = Command{
		Handler: i.pregameCommands["news"].Handler,
		Help:    i.pregameCommands["news"].Help,
	}

	//Phasers command
	i.gowarsCommands["phasers"] = Command{
		Handler: func(args []string, conn net.Conn) string {
			// Parse arguments: [Absolute|Relative|Computed] [energy] <vpos> <hpos> | <shipname>

			// Check if no arguments provided - show prompt
			if len(args) == 0 {
				return "phasers absolute <vpos> <hpos>\r\nphasers relative <vpos> <hpos>\r\nphasers computed <shipname>\r\nphasers <vpos> <hpos>"
			}

			// Support ? parameter for help
			if len(args) == 1 && args[0] == "?" {
				return "phasers absolute <vpos> <hpos>\r\nphasers relative <vpos> <hpos>\r\nphasers computed <shipname>\r\nphasers <vpos> <hpos>"
			}

			// Check for mode parameter with abbreviation support
			validModes := map[string]bool{"absolute": true, "relative": true, "computed": true}
			if mode, ok := i.resolveParameter(strings.ToLower(args[0]), validModes); ok {
				switch mode {
				case "absolute":
					return i.phaserSimple("absolute", args[1:], conn)
				case "relative":
					return i.phaserSimple("relative", args[1:], conn)
				case "computed":
					// Check if attacker's computer has more than CriticalDamage
					info, ok := i.connections.Load(conn)
					if ok {
						connInfo := info.(ConnectionInfo)
						ship := i.getShipByName(connInfo.Galaxy, connInfo.Shipname)
						if ship != nil && ship.ComputerDamage > CriticalDamage {
							return "Computer inoperative."
						}
					}

					return i.phaserSimple("computed", args[1:], conn)
				default:
					return "Invalid mode for phasers command"
				}
			} else {
				// Try to parse as simple coordinates (vpos hpos) or (energy vpos hpos)
				if len(args) == 2 {
					// Format: ph vpos hpos - use simple coordinate mode
					return i.phaserSimple("", args, conn)
				} else if len(args) == 3 {
					// Format: ph energy vpos hpos - use simple coordinate mode
					return i.phaserSimple("", args, conn)
				}
				return "Invalid syntax.\r\nSyntax:\r\nPHasers <vpos> <hpos>\r\nPHasers [Absolute|Relative] [energy] <vpos> <hpos>\r\nPHasers Computed [energy] <shipname>"
			}
		},
		Help: "Fire PHASERS at an enemy ship, base, or planet\r\n" +
			"Syntax: PHasers [Absolute|Relative|Computed] [energy] <vpos> <hpos>\r\n" +
			"\n" +
			"Phasers must be directed at a specific target, and only one target may\r\n" +
			"be specified per command. Obstacles seemingly in the path of the\r\n" +
			"phaser blast are unaffected, since the energy ray is not a line-of-\r\n" +
			"sight weapon. The size of the hit is inversely proportional to the\r\n" +
			"distance from the target. Maximum range is 10 sectors vertically,\r\n" +
			"horizontally, or diagonally. Each phaser blast consumes 200 units of\r\n" +
			"ship energy, unless a specific amount of energy is given (the\r\n" +
			"specified energy must be between 50 and 500 units, inclusive). The\r\n" +
			"phaser banks have roughly a 5% chance of damage with a default (200\r\n" +
			"unit) blast, with the probability of damage reaching nearly 65% with a\r\n" +
			"maximum (500 unit) blast. The severity of the resulting damage is\r\n" +
			"also dependant on the size of the blast. Also, if your ship's shields\r\n" +
			"are up, a high-speed shield control is used to quickly lower and then\r\n" +
			"restore the shields during the fire. This procedure consumes another\r\n" +
			"200 units of ship energy. The weapons officer on board your ship will\r\n" +
			"cancel all phaser blasts directed against friendly ships, bases, or\r\n" +
			"planets. Firing phasers (or getting hit by phasers) puts you on red\r\n" +
			"alert. NOTE: Although phasers can damage enemy planetary\r\n" +
			"installations (BUILDs), they can NOT destroy the planet itself.\r\n" +
			"\r\n" +
			"Examples:\r\n" +
			"PH 12 32                Phaser target at sector 12-32.\r\n" +
			"PH A 12 32              Equivalent to \"PH 12 32\".\r\n" +
			"PH R 2 -3               Phaser target at sector 12-32, if your location is\r\n" +
			"                        10-35.\r\n" +
			"PH C BUZZARD            Phaser the Buzzard (if in range).\r\n" +
			"PH C B                  Same as PH C BUZZARD (ship names can be abbreviated to\r\n" +
			"                        1 character).\r\n" +
			"PH 300 12 32            Phaser target at sector 12-32, using 300 units of\r\n" +
			"                        energy.",
	}
	i.gowarsCommands["planets"] = Command{
		Handler: func(args []string, conn net.Conn) string {
			// Supported optional parameters and their abbreviations
			validParams := map[string]bool{"summary": true, "all": true}
			subParams := map[string]bool{"neutral": true, "captured": true}

			// Abbreviation support for main parameter
			mainParam := ""
			if len(args) > 0 {
				if resolved, ok := i.resolveParameter(strings.ToLower(args[0]), validParams); ok {
					mainParam = resolved
				}
			}

			// Handle abbreviation for sub-parameters under "all"
			subParam := ""
			if mainParam == "all" && len(args) > 1 {
				if resolved, ok := i.resolveParameter(strings.ToLower(args[1]), subParams); ok {
					subParam = resolved
				} else if _, err := strconv.Atoi(args[1]); err == nil {
					subParam = args[1] // Numeric range
				}
			}

			// Parameter completion and prompting for partial input
			if len(args) > 0 && strings.HasSuffix(args[0], "?") {
				return "planets sum | all"
			}
			if mainParam == "all" && len(args) > 1 && strings.HasSuffix(args[1], "?") {
				return "planets all neutral | captured | <range>"
			}

			// Handle "planets sum" (abbreviated or full)
			if mainParam == "summary" {
				// Output the same as "summary planets"
				return i.gowarsCommands["summary"].Handler([]string{"planets"}, conn)
			}

			// Handle "planets all" (abbreviated or full)
			if mainParam == "all" {
				if subParam == "neutral" {
					// Delegate to list neutral planets
					return i.gowarsCommands["list"].Handler([]string{"neutral", "planets"}, conn)
				}
				if subParam == "captured" {
					// Delegate to list captured planets
					return i.gowarsCommands["list"].Handler([]string{"captured"}, conn)
				}
				if subParam != "" {
					// If subParam is a number, treat as range and delegate to list planets <range>
					if _, err := strconv.Atoi(subParam); err == nil {
						return i.gowarsCommands["list"].Handler([]string{"planets", subParam}, conn)
					}
					return fmt.Sprintf("Planets within range %s: [list would go here]", subParam)
				}
				return "planets all neutral | captured | <range>"
			}

			// Default: planets command with no parameters behaves like list planets 10
			if len(args) == 0 {
				return i.gowarsCommands["list"].Handler([]string{"planets", "10"}, conn)
			}

			return "Stub: planets command (no parameters)."
		},
		Help: "List various PLANET information\r\n" +
			"Syntax: PLanets [<keywords>]\r\n" +
			"\r\n" +
			"List location and number of builds for all known planets, and a\r\n" +
			"summary of planets within a specified range or the entire galaxy. The\r\n" +
			"default range is 10 sectors, and the default side is every side. See\r\n" +
			"the help for LIST for more information and the complete set of\r\n" +
			"keywords that can be used to modify PLANETS output.\r\n" +
			"\n" +
			"Examples:\n" +
			"PL                      List all planets within 10 sectors.\r\n" +
			"PL SUM                  Give summary of all planets in game.\r\n" +
			"PL ALL NEU              List all known neutral planets.\r\n" +
			"PL ALL CAP              List all known captured planets.\r\n" +
			"PL ALL 20               List all known planets within a radius of 20 sectors.",
	}
	i.gowarsCommands["radio"] = Command{
		Handler: func(args []string, conn net.Conn) string {
			// Accepts only "on" or "off" (with abbreviation support)
			validParams := map[string]bool{"on": true, "off": true}
			if len(args) == 0 {
				return "Usage: radio on | off"
			}
			// Parameter completion
			if len(args) == 1 && strings.HasSuffix(args[0], "?") {
				prefix := strings.ToLower(strings.TrimSuffix(args[0], "?"))
				var matches []string
				for param := range validParams {
					if strings.HasPrefix(param, prefix) {
						matches = append(matches, param)
					}
				}
				if len(matches) == 0 {
					return "radio on | off"
				}
				return "radio " + strings.Join(matches, " | ")
			}
			// Abbreviation support
			param, ok := i.resolveParameter(strings.ToLower(args[0]), validParams)
			if !ok {
				return "Error: parameter must be 'on' or 'off'"
			}
			// Find user's ship
			info, okConn := i.connections.Load(conn)
			if !okConn || info.(ConnectionInfo).Shipname == "" {
				return "Error: you must be in GOWARS with a shipname to use radio"
			}
			connInfo := info.(ConnectionInfo)
			shipname := connInfo.Shipname
			galaxy := connInfo.Galaxy
			for idx := range i.objects {
				obj := i.objects[idx]
				if obj.Type == "Ship" && obj.Name == shipname && obj.Galaxy == galaxy {
					switch param {
					case "on":
						obj.RadioOnOff = true
						return "Radio turned on, Captain."
					case "off":
						obj.RadioOnOff = false
						return "Radio turned off, Captain."
					}
				}
			}
			return "Error: ship not found"
		},
		Help: "Turn sub-space RADIO on or off, or\r\n" +
			"set to ignore or restore communications from individual ships\r\n" +
			"Syntax: RAdio ON|OFf or RAdio Gag|Ungag <ship name>\r\n" +
			"\r\n" +
			"Turn your ship's sub-space radio on or off, thus controlling whether\r\n" +
			"or not you'll receive any messages from other ships or your bases; or\r\n" +
			"suppress or restore messages originating from specific ships.\r\n" +
			"\r\n" +
			"Examples:\r\n" +
			"RA ON                   Turn sub-space radio ON.\r\n" +
			"RA OFF                  Turn sub-space radio OFF.\r\n" +
			"RA G L                  Suppress all radio messages sent by the Lexington\r\n" +
			"RA U W                  Allow radio messages sent by the Wolf to be received.",
	}

	i.gowarsCommands["scan"] = Command{
		Handler: func(args []string, conn net.Conn) string {
			return i.handleScanCtx(context.Background(), DefScanRange, args, conn)
		},
		Help: "Full range SCAN\r\n" +
			"Syntax: SCan [Up|Down|Right|Left|Corner] [<range>|<vr><hr>] [W]\r\n" +
			"\r\n" +
			"Display a selected portion of the nearby universe. If no range is\r\n" +
			"specified, SCAN defaults to a square scan range of ten sectors from\r\n" +
			"the present ship location. The keywords UP, DOWN, RIGHT, LEFT, and\r\n" +
			"CORNER modify this to include only the part of this original square\r\n" +
			"specified (relative to the ship). The maximum scan range is 10\r\n" +
			"sectors, and larger specified ranges are reduced to this value. If\r\n" +
			"individual vertical and horizontal ranges are specified, the scanning\r\n" +
			"field will be shaped accordingly. The WARNING keyword if added to the\r\n" +
			"end of a SCAN command string will flag the empty sectors within range\r\n" +
			"of an enemy base or planet with !'s instead of .'s. The SCAN symbols\r\n" +
			"and their meanings are:\r\n" +
			"E,F,I,L,N,S,T,V,Y Federation warships\r\n" +
			"B,C,D,G,H,J,M,P,W Empire warships\r\n" +
			"        ~~ Romulan warship\r\n" +
			"        [] Federation starbase\r\n" +
			"        () Empire starbase\r\n" +
			"         @ Neutral planet\r\n" +
			"        +@ Federation planet\r\n" +
			"        -@ Empire planet\r\n" +
			"         * Star\r\n" +
			"                  Black hole\r\n" +
			"         . Empty sector\r\n" +
			"         ! Empty sector within range of enemy port (only when\r\n" +
			"                  using WARNING keyword)\r\n" +
			"\r\n" +
			"Examples:\r\n" +
			"  SC                      Scan universe within a radius 10 sectors.\r\n" +
			"  SC 10                   Equivalent to \"SC\".\r\n" +
			"  SC 13                   Equivalent to \"SC 10\" or \"SC\".\r\n" +
			"  SC 4                    Scan universe within 4 sectors.\r\n" +
			"  SC 4 4                  Equivalent to \"SC 4\".\r\n" +
			"  SC 2 8                  Scan up to 5 rows and 17 columns, centered on the\r\n" +
			"                          present ship location.\r\n" +
			"  SC U 4 7                Show only upper half of normal \"SC 4 7\" scan.\r\n" +
			"  SC C -5 -5              Scan the region bounded by the present ship location\r\n" +
			"                          and the location (-5,-5) sectors away (puts ship in\r\n" +
			"                          upper right corner of the scan).\r\n" +
			"  SC W                    Same as \"SC\", plus shows danger zones around enemy\r\n" +
			"                          bases and planets.",
	}

	i.gowarsCommands["srscan"] = Command{
		Handler: func(args []string, conn net.Conn) string {
			return i.handleScanCtx(context.Background(), 14, args, conn)
		},
		Help: "Short Range SCAN\r\n" +
			"Syntax: SRscan [Up|Down|Right|Left|Corner] [<range>|<vr><hr>] [W]\r\n" +
			"\r\n" +
			"Equivalent to SCAN, but with a default scan range of 7 sectors. For\r\n" +
			"complete information on sensor scans, see the help on SCAN.",
	}

	i.gowarsCommands["set"] = Command{
		Handler: func(args []string, conn net.Conn) string {
			interp := i
			// Sub-parameter definitions
			paramOptions := map[string]bool{"prompt": true, "output": true, "OCdef": true, "scan": true, "icdef": true, "name": true, "baud": true}
			outputOptions := map[string]bool{"long": true, "medium": true, "short": true}
			OCdefOptions := map[string]bool{"relative": true, "absolute": true, "both": true}
			scanOptions := map[string]bool{"long": true, "short": true}
			promptOptions := map[string]bool{"normal": true, "informative": true}
			icdefOptions := map[string]bool{"relative": true, "absolute": true}
			baudOptions := map[string]bool{"0": true, "300": true, "1200": true, "2400": true, "9600": true}

			var prompt, output, OCdef, scan, icdef, name string
			var baud int
			var baudProvided bool
			var errMsg string
			if len(args) == 0 {
				// Print current settings
				info, ok := i.connections.Load(conn)
				if !ok {
					return "Error: connection not found"
				}
				connInfo := info.(ConnectionInfo)
				// Find the player's ship side if in gowars
				shipSide := ""
				if connInfo.Section == "gowars" && connInfo.Shipname != "" {
					for _, obj := range i.objects {
						if obj.Type == "Ship" && obj.Name == connInfo.Shipname && obj.Galaxy == connInfo.Galaxy {
							shipSide = obj.Side
							break
						}
					}
				}
				if shipSide == "" {
					shipSide = "(not in gowars)"
				}
				return fmt.Sprintf(
					"Current settings:\r\n  side: %s\r\n  output: %s\r\n  OCdef: %s\r\n  scan: %s\r\n  ICdef: %s\r\n  name: %s\r\n  prompt: %s\r\n  baud: %d\r\n  administrator: %s",
					shipSide,
					connInfo.OutputState,
					connInfo.OCdef,
					connInfo.Scan,
					connInfo.ICdef,
					connInfo.Name,
					func() string {
						if connInfo.Prompt != "" {
							return connInfo.Prompt
						} else {
							return "normal"
						}
					}(),
					connInfo.BaudRate,
					func() string {
						if connInfo.AdminMode == true {
							return "true"
						} else {
							return "false"
						}
					}(),
				)
			}

			// Handle ? parameter completion
			for i, arg := range args {
				if strings.HasSuffix(arg, "?") {
					prefix := strings.ToLower(strings.TrimSuffix(arg, "?"))
					if i == 0 {
						// First parameter - show available parameters
						var matches []string
						parameters := []string{"prompt", "output", "OCdef", "scan", "icdef", "name", "baud"}
						for _, param := range parameters {
							if strings.HasPrefix(strings.ToLower(param), prefix) {
								matches = append(matches, param)
							}
						}
						if len(matches) == 0 {
							return "Error: No valid completion for parameter"
						}
						// Format as multiline, matching requested style
						var lines []string
						lines = append(lines, "Command: set")
						for _, param := range matches {
							// Capitalize first letter
							lines = append(lines, "set "+strings.Title(param))
						}
						return strings.Join(lines, "\r\n")
					} else if i == 1 {
						// Second parameter - show values for the first parameter
						param := strings.ToLower(args[0])
						switch param {
						case "prompt":
							return "set prompt Normal | Informative"
						case "output":
							return "set output long | medium | short"
						case "ocdef":
							return "set ocdef relative | absolute | both"
						case "scan":
							return "set scan long | short"
						case "icdef":
							return "set icdef relative | absolute"
						case "name":
							return "set name <string>"
						case "baud":
							return "set baud 0 | 300 | 1200 | 2400 | 9600"
						default:
							return "Error: Unknown parameter"
						}
					}
				}
			}

			for i := 0; i < len(args); i++ {
				param, ok := interp.resolveParameter(args[i], paramOptions)
				if !ok {
					return fmt.Sprintf("Error: unknown parameter '%s'. Valid parameters are: prompt, output, OCdef, scan, icdef, name, baud", args[i])
				}
				switch param {
				case "prompt":
					if i+1 < len(args) {
						val, ok := interp.resolveParameter(args[i+1], promptOptions)
						if !ok {
							errMsg = "Error: prompt parameter requires a value (Normal or Informative)"
							break
						}
						prompt = val
						i++ // Skip the value
					} else {
						errMsg = "Error: prompt parameter requires a value (Normal or Informative)"
					}
				case "output":
					if i+1 < len(args) {
						val, ok := interp.resolveParameter(args[i+1], outputOptions)
						if !ok {
							errMsg = "Error: output parameter requires a value (long, medium, or short)"
							break
						}
						output = val
						i++ // Skip the value
					} else {
						errMsg = "Error: output parameter requires a value (long, medium, or short)"
					}
				case "OCdef":
					if i+1 < len(args) {
						val, ok := interp.resolveParameter(args[i+1], OCdefOptions)
						if !ok {
							errMsg = "Error: OCdef parameter requires a value (relative, absolute, or both)"
							break
						}
						OCdef = val
						i++ // Skip the value
					} else {
						errMsg = "Error: OCdef parameter requires a value (relative, absolute, or both)"
					}
				case "scan":
					if i+1 < len(args) {
						val, ok := interp.resolveParameter(args[i+1], scanOptions)
						if !ok {
							errMsg = "Error: scan parameter requires a value (long or short)"
							break
						}
						scan = val
						i++ // Skip the value
					} else {
						errMsg = "Error: scan parameter requires a value (long or short)"
					}
				case "icdef":
					if i+1 < len(args) {
						val, ok := interp.resolveParameter(args[i+1], icdefOptions)
						if !ok {
							errMsg = "Error: icdef parameter requires a value (relative or absolute)"
							break
						}
						icdef = val
						i++ // Skip the value
					} else {
						errMsg = "Error: icdef parameter requires a value (relative or absolute)"
					}
				case "name":
					if i+1 < len(args) {
						name = args[i+1]
						i++ // Skip the value
					} else {
						errMsg = "Error: name parameter requires a value (string)"
					}
				case "baud":
					if i+1 < len(args) {
						val, ok := interp.resolveParameter(args[i+1], baudOptions)
						if !ok {
							errMsg = "Error: baud parameter requires a value (0, 300, 1200, 2400, or 9600)"
							break
						}
						baud, _ = strconv.Atoi(val)
						baudProvided = true
						i++ // Skip the value
					} else {
						errMsg = "Error: baud parameter requires a value (0, 300, 1200, 2400, or 9600)"
					}
				}
				if errMsg != "" {
					return errMsg
				}
			}

			// Validate sub-parameters (redundant, but keeps error messages consistent)
			if output != "" && output != "long" && output != "medium" && output != "short" {
				return "Error: output parameter must be 'long', 'medium', or 'short'"
			}
			if OCdef != "" && OCdef != "relative" && OCdef != "absolute" && OCdef != "both" {
				return "Error: OCdef parameter must be 'relative', 'absolute', or 'both'"
			}
			if scan != "" && scan != "long" && scan != "short" {
				return "Error: scan parameter must be 'long' or 'short'"
			}
			if prompt != "" && prompt != "normal" && prompt != "informative" {
				return "Error: prompt parameter must be 'Normal' or 'Informative'"
			}
			if icdef != "" && icdef != "relative" && icdef != "absolute" {
				return "Error: icdef parameter must be 'relative' or 'absolute'"
			}
			if baud != 0 && baud != 300 && baud != 1200 && baud != 2400 && baud != 9600 {
				return "Error: baud parameter must be '0', '300', '1200', '2400', or '9600'"
			}

			// Return stub messages for each parameter
			var stubMessages []string
			if prompt != "" {
				// Set the prompt mode for this connection
				info, ok := i.connections.Load(conn)
				if !ok {
					return "Error: connection not found"
				}
				connInfo := info.(ConnectionInfo)
				connInfo.Prompt = prompt
				i.connections.Store(conn, connInfo)
				stubMessages = append(stubMessages, fmt.Sprintf("Prompt mode set to: %s", prompt))
			}
			if output != "" {
				// Set the output state for this connection
				info, ok := i.connections.Load(conn)
				if !ok {
					return "Error: connection not found"
				}
				connInfo := info.(ConnectionInfo)
				connInfo.OutputState = output
				i.connections.Store(conn, connInfo)
				stubMessages = append(stubMessages, fmt.Sprintf("Output state set to %s", output))
			}
			if OCdef != "" {
				// Set the OCdef state for this connection
				info, ok := i.connections.Load(conn)
				if !ok {
					return "Error: connection not found"
				}
				connInfo := info.(ConnectionInfo)
				connInfo.OCdef = OCdef
				i.connections.Store(conn, connInfo)
				stubMessages = append(stubMessages, fmt.Sprintf("OCdef set to %s", OCdef))
			}
			if scan != "" {
				// Set the scan state for this connection
				info, ok := i.connections.Load(conn)
				if !ok {
					return "Error: connection not found"
				}
				connInfo := info.(ConnectionInfo)
				connInfo.Scan = scan
				i.connections.Store(conn, connInfo)
				stubMessages = append(stubMessages, fmt.Sprintf("Scan set to %s", scan))
			}
			if icdef != "" {
				// Set the icdef state for this connection
				info, ok := i.connections.Load(conn)
				if !ok {
					return "Error: connection not found"
				}
				connInfo := info.(ConnectionInfo)
				connInfo.ICdef = icdef
				i.connections.Store(conn, connInfo)
				stubMessages = append(stubMessages, fmt.Sprintf("ICdef set to %s", icdef))
			}
			if name != "" {
				// Sanitize and validate the name
				sanitizedName, errMsg := sanitizeName(name)
				if errMsg != "" {
					return errMsg
				}
				info, ok := i.connections.Load(conn)
				if !ok {
					return "Error: connection not found"
				}
				connInfo := info.(ConnectionInfo)
				connInfo.Name = sanitizedName
				i.connections.Store(conn, connInfo)
				stubMessages = append(stubMessages, fmt.Sprintf("Name set to %s", sanitizedName))
			}
			if baudProvided {
				// Prevent setting baud to 0 if DecwarMode is true
				info, ok := i.connections.Load(conn)
				if DecwarMode == true && baud == 0 {
					if !ok || !info.(ConnectionInfo).AdminMode {
						return "Only administrators can change their baud rate to 0 (no delay)"
					}
				}
				// Set the baud rate for this connection
				if !ok {
					return "Error: connection not found"
				}
				connInfo := info.(ConnectionInfo)
				connInfo.BaudRate = baud
				i.connections.Store(conn, connInfo)
				if baud == 0 {
					stubMessages = append(stubMessages, "Baud rate set to 0 (no delay)")
				} else {
					stubMessages = append(stubMessages, fmt.Sprintf("Baud rate set to %d", baud))
				}
			}

			// If no parameters provided, return usage
			if len(stubMessages) == 0 {
				return "Usage: set <parameter> <value>. Parameters: prompt (Normal/Informative), output (long/medium/short), OCdef (relative/absolute/both), scan (long/short), icdef (relative/absolute), name (string), baud (0/300/1200/2400/9600)"
			}

			return strings.Join(stubMessages, "\r\n")
		},
		Help: "SET input and output parameters\r\n" +
			"Syntax: SEt <keyword> <value>\r\n" +
			"\r\n" +
			"Keyword Value    Description\r\n" +
			"------- -----    -----------\r\n" +
			"Name    name     Change name (shows in USERS).\r\n" +
			"Output  Long     Default. Use longest output format.\r\n" +
			"        Medium   Use medium output format.\r\n" +
			"        Short    Use short (cryptic) output format.\r\n" +
			"Scan    Long     Default. Use long format scans.\r\n" +
			"        Short    Use 1 character symbols instead of 2.\r\n" +
			"Prompt  Normal   Default. Use \"COMMAND: \" prompt.\r\n" +
			"        Informative Use \"> \" for prompt. Precede the \">\" with:\r\n" +
			"                 S if shields are down or < 10%.\r\n" +
			"                 E if ship energy < 1000 (yellow alert).\r\n" +
			"                 D if ship damage > 2000.\r\n" +
			"                 nL if life support is critically damaged (n stardates\r\n" +
			"                 of reserves).\r\n" +
			"Ttytype CRT, ADM-3a, ADM-2, SOROC, BEEHIVE, ACT-IV, ACT-V, VT05, VT06,\r\n" +
			"                 VT50, VT52, VT100\r\n" +
			"                 Tells DECWAR the TTY type so that it can do rubout, R\r\n" +
			"                 and U properly\r\n" +
			"OCdef   Absolute Default. Display all coordinates in absolute format\r\n" +
			"                 (vpos-hpos).\r\n" +
			"        Relative Display coordinates relative to your location\r\n" +
			"                 (dv,dh).\r\n" +
			"        Both     Display coordinates in both absolute and relative\r\n" +
			"                 form.\r\n" +
			"Icdef   Absolute Default. All input coordinates default to absolute.\r\n" +
			"        Relative Input coordinates default to relative.\r\n" +
			"Baud    0        Change the baud rate to a simulated speed, 0 defaulted on gowars\r\n" +
			"        300\r\n" +
			"        1200\r\n" +
			"        2400\r\n" +
			"        9600\r\n" +
			"\r\n" +
			"Examples:\r\n" +
			"SE PR I          Switch to informative prompt.\r\n" +
			"SE OU S          Set output format to short.\r\n" +
			"SE N THOR        Change your name in USERS to THOR.",
	}
	i.gowarsCommands["shields"] = Command{
		Handler: func(args []string, conn net.Conn) string {
			// Accepts "up", "down", or "transfer <value>" (with abbreviation support)
			validParams := map[string]bool{"up": true, "down": true, "transfer": true}
			if len(args) == 0 {
				return "Usage: shields up | down | transfer <value>"
			}
			// Parameter completion
			if len(args) == 1 && strings.HasSuffix(strings.ToLower(args[0]), "?") {
				prefix := strings.ToLower(strings.TrimSuffix(args[0], "?"))
				var matches []string
				for param := range validParams {
					if strings.HasPrefix(param, prefix) {
						matches = append(matches, param)
					}
				}
				if len(matches) == 0 {
					return "shields up | down | transfer"
				}
				return "shields " + strings.Join(matches, " | ")
			}
			// Abbreviation support
			param, ok := i.resolveParameter(strings.ToLower(args[0]), validParams)
			if !ok {
				return "Error: parameter must be 'up', 'down', or 'transfer'"
			}
			// "shields transfer" requires a value
			if param == "transfer" {
				if len(args) < 2 {
					return "Usage: shields transfer <value>"
				}

				// Validate value is a number (can be negative)
				valStr := args[1]
				if strings.HasSuffix(valStr, "?") {
					return "shields transfer <value>"
				}
				ste, err := strconv.ParseFloat(valStr, 32) //amount requested to transfer
				if err != nil {
					return "Error: shields transfer requires a numeric value"
				}
				shieldTransEng := float32(ste)

				// Find user's ship
				info, okConn := i.connections.Load(conn)
				if !okConn || info.(ConnectionInfo).Shipname == "" {
					return "Error: you must be in GOWARS with a shipname to use shields"
				}

				connInfo := info.(ConnectionInfo)
				shipname := connInfo.Shipname
				galaxy := connInfo.Galaxy
				for idx := range i.objects {
					obj := i.objects[idx]
					if obj.Type == "Ship" && obj.Name == shipname && obj.Galaxy == galaxy {
						// Shield Tramsfer work:
						if shieldTransEng < 0 { // Transfer  from shields
							if InitialShieldValue-int(shieldTransEng*10) < obj.Shields { //Enough shield energy?
								obj.ShipEnergy = obj.ShipEnergy + int(shieldTransEng*10) //Remove FROM ship energy
								obj.Shields = obj.Shields - int(shieldTransEng*10)       //Add it to shield energy
								return "Energy transferred, Captain."
							} else { // Transfer to shields
								obj.ShipEnergy = obj.ShipEnergy - int(shieldTransEng*10) // Remove TO ship energy
								obj.Shields = obj.Shields + int(shieldTransEng*10)
								if obj.Shields < 0 { //Give excess shield energy back to ship
									obj.ShipEnergy = obj.ShipEnergy + obj.Shields
									obj.Shields = 0 //Should trigger death
								}
								if obj.ShipEnergy > InitialShipEnergy {
									obj.Shields = obj.Shields + (obj.ShipEnergy - InitialShipEnergy)
									obj.ShipEnergy = InitialShipEnergy
								}

								return "Energy transferred, Captain."
							}
						} else {
							if InitialShieldValue-int(shieldTransEng*10) < obj.Shields { //Enough shield energy?
								obj.ShipEnergy = obj.ShipEnergy - int(shieldTransEng*10) //Transfer FROM ship energy
								obj.Shields = obj.Shields + int(shieldTransEng*10)       //Add it to shield energy
								if obj.ShipEnergy < 0 {                                  //Give excess shield energy back to ship
									obj.Shields = obj.Shields + obj.ShipEnergy
									obj.ShipEnergy = 0
								}
								if obj.Shields > InitialShieldValue {
									obj.ShipEnergy = obj.ShipEnergy + (obj.Shields - InitialShieldValue)
									obj.Shields = InitialShieldValue
								}
								return "Energy transferred, Captain."
							} else { // Trmasfer to shields
								obj.ShipEnergy = obj.ShipEnergy - int(shieldTransEng*10) // Transfer TO ship energy
								obj.Shields = obj.Shields + int(shieldTransEng*10)
								return "Energy transferred, Captain."
							}
						}

					}
				}
			}
			// Find user's ship
			info, okConn := i.connections.Load(conn)
			if !okConn || info.(ConnectionInfo).Shipname == "" {
				return "Error: you must be in GOWARS with a shipname to use shields"
			}
			connInfo := info.(ConnectionInfo)
			shipname := connInfo.Shipname
			galaxy := connInfo.Galaxy
			for idx := range i.objects {
				obj := i.objects[idx]
				if obj.Name == shipname && obj.Galaxy == galaxy {
					switch param {
					case "up":
						// Set shields up
						obj.ShieldsUpDown = true
						// Raising shields consumes 100 units of ship energy
						obj.ShipEnergy = obj.ShipEnergy - 1000
						// Raising shields will cause the tractor beam to be broken
						if obj.TractorOnOff && obj.TractorShip != "" {
							// Find other ship and clear its tractor state
							for j := range i.objects {
								other := i.objects[j]
								if other.Name == obj.TractorShip && other.Galaxy == connInfo.Galaxy {
									other.TractorOnOff = false
									other.TractorShip = ""
									// Notify the other ship that the tractor beam is broken
									i.notifyShipTractorBroken(other.Name, other.Galaxy)
									break
								}
							}
							// Clear this ship's tractor state
							obj.TractorOnOff = false
							obj.TractorShip = ""
						}
						return "Shields raised, Captain."
					case "down":
						// Set shields down
						obj.ShieldsUpDown = false
						return "Shields lowered, Captain."
					}
				}
			}
			return "Error: ship not found"
		},
		Help: "SHIELD control\r\n" +
			"Syntax: SHields Up|Down or SHields Transfer <energy>\r\n" +
			"\r\n" +
			"Raise or lower ship shields, or transfer energy between ship and\r\n" +
			"shield energy reserves. Raising shields consumes 100 units of ship\r\n" +
			"energy, lowering them or transfering energy is \"free\". NOTE: Shield\r\n" +
			"condition is displayed as +n% for shields up, n% of full strength, or\r\n" +
			"-n%, for shields down, n% of full strength.\r\n" +
			"\r\n" +
			"Examples:\r\n" +
			"SH U                    Raise shields.\r\n" +
			"SH D                    Lower shields.\r\n" +
			"SH T 500                Transfer 500 units of energy TO shields\r\n" +
			"SH T -500               Transfer 500 units of energy FROM shields",
	}
	i.gowarsCommands["srscan"] = Command{
		Handler: i.gowarsCommands["srscan"].Handler,
		Help: "Short Range SCAN\r\n" +
			"Syntax: SRscan [Up|Down|Right|Left|Corner] [<range>|<vr><hr>] [W]\r\n" +
			"\r\n" +
			"Equivalent to SCAN, but with a default scan range of 7 sectors. For\r\n" +
			"complete information on sensor scans, see the help on SCAN.\r\n",
	}
	i.gowarsCommands["status"] = Command{
		Handler: func(args []string, conn net.Conn) string {
			return i.handleStatus(args, conn)
		},
		Help: "Show ship STATUS\r\n" +
			"Syntax:\r\n" +
			"STatus [Condition|Location|Torpedoes|Energy|Damage|Shields|Radio]\r\n" +
			"\r\n" +
			"Show the current stardate, plus the status of any of the ship\r\n" +
			"attributes: ship condition, location, number of torps, ship energy,\r\n" +
			"ship damage, shield energy, and radio condition. Ship condition can\r\n" +
			"be green, yellow (low on energy), or red (in battle). Radio condition\r\n" +
			"is either on or off.\r\n" +
			"\r\n" +
			"Examples:\r\n" +
			"ST                      Give full status report.\r\n" +
			"ST T                    Report how many torpedos remain on board.\r\n" +
			"ST E D SH               Report the ship energy, the ship damage, and the\r\n" +
			"                        shield condition (energy, %, up/down).\r\n" +
			"ST L                    Report the current ship location.",
	}
	i.gowarsCommands["targets"] = Command{
		Handler: func(args []string, conn net.Conn) string {
			// Parameter prompting and tab completion
			// List of canonical parameters (for prompting and completion)
			params := []string{"ships", "bases", "planets", "all", "romulan", "closest", "list", "summary", "<radius>"}
			abbrMap := map[string]string{
				"ships":    "sh",
				"bases":    "ba",
				"planets":  "pl",
				"all":      "a",
				"romulan":  "rom",
				"closest":  "cl",
				"list":     "li",
				"summary":  "su",
				"<radius>": "r",
			}
			// Map of all valid keywords and their stub messages, including abbreviations
			stubParams := map[string]string{
				"ships":   "Stub: targets ships (list enemy ships in range)",
				"ship":    "Stub: targets ships (list enemy ships in range)",
				"sh":      "Stub: targets ships (list enemy ships in range)",
				"s":       "Stub: targets ships (list enemy ships in range)",
				"bases":   "Stub: targets bases (list enemy bases in range)",
				"base":    "Stub: targets bases (list enemy bases in range)",
				"ba":      "Stub: targets bases (list enemy bases in range)",
				"b":       "Stub: targets bases (list enemy bases in range)",
				"planets": "Stub: targets planets (list enemy planets in range)",
				"planet":  "Stub: targets planets (list enemy planets in range)",
				"pl":      "Stub: targets planets (list enemy planets in range)",
				"p":       "Stub: targets planets (list enemy planets in range)",
				"all":     "Stub: targets all (list all enemy objects in range)",
				"a":       "Stub: targets all (list all enemy objects in range)",
				"romulan": "Stub: targets romulan (list Romulan ships in range)",
				"rom":     "Stub: targets romulan (list Romulan ships in range)",
				"r":       "Stub: targets romulan (list Romulan ships in range)",
				"closest": "Stub: targets closest (show closest enemy target)",
				"close":   "Stub: targets closest (show closest enemy target)",
				"cl":      "Stub: targets closest (show closest enemy target)",
				"c":       "Stub: targets closest (show closest enemy target)",
				"list":    "Stub: targets list (list all targets in detail)",
				"li":      "Stub: targets list (list all targets in detail)",
				"l":       "Stub: targets list (list all targets in detail)",
				"summary": "Stub: targets summary (show summary of targets in range)",
				"sum":     "Stub: targets summary (show summary of targets in range)",
				"su":      "Stub: targets summary (show summary of targets in range)",
			}

			// If no args, delegate to list targets (default radius 10)
			if len(args) == 0 {
				return i.gowarsCommands["list"].Handler([]string{"targets"}, conn)
			} else if len(args) == 1 && (args[0] == "?" || args[0] == "") {
				var stubs []string
				for _, param := range params {
					stubs = append(stubs, fmt.Sprintf("targets %s", param))
				}
				return strings.Join(stubs, "\r\n")
			}
			if len(args) == 1 && strings.HasSuffix(args[0], "?") {
				prefix := strings.ToLower(strings.TrimSuffix(args[0], "?"))
				var matches []string
				for _, param := range params {
					abbr := abbrMap[param]
					if strings.HasPrefix(strings.ToLower(param), prefix) || strings.HasPrefix(abbr, prefix) {
						matches = append(matches, param)
					}
				}
				if len(matches) == 0 {
					return "Error: No valid completion for targets parameter"
				}
				return "targets " + strings.Join(matches, " | ")
			}

			// Check for stub parameters and delegate "targets ships" to "list targets ships"
			for _, arg := range args {
				lowerArg := strings.ToLower(arg)
				switch lowerArg {
				case "ships", "ship", "sh", "s":
					// Delegate to list targets ships for consistent output
					return i.gowarsCommands["list"].Handler([]string{"targets", "ships"}, conn)
				case "bases", "base", "ba", "b":
					return i.gowarsCommands["list"].Handler([]string{"targets", "bases"}, conn)
				case "planets", "planet", "pl", "p":
					return i.gowarsCommands["list"].Handler([]string{"targets", "planets"}, conn)
				case "all", "a":
					return i.gowarsCommands["list"].Handler([]string{"targets", "all"}, conn)
				case "romulan", "rom", "r":
					return i.gowarsCommands["list"].Handler([]string{"targets", "romulan"}, conn)
				case "closest", "close", "cl", "c":
					return i.gowarsCommands["list"].Handler([]string{"targets", "closest"}, conn)
				case "list", "li", "l":
					return i.gowarsCommands["list"].Handler([]string{"targets", "list"}, conn)
				case "summary", "sum", "su":
					return i.gowarsCommands["list"].Handler([]string{"targets", "summary"}, conn)
				}
				if msg, ok := stubParams[lowerArg]; ok {
					return msg
				}
			}

			// If first argument is a positive integer (radius), delegate to list targets <radius>
			if len(args) == 1 {
				if r, err := strconv.Atoi(args[0]); err == nil && r > 0 {
					return i.gowarsCommands["list"].Handler([]string{"targets", args[0]}, conn)
				}
			}

			// Default radius if not provided or if first arg is not a stub param
			radius := 10
			if len(args) >= 1 {
				if r, err := strconv.Atoi(args[0]); err == nil && r > 0 {
					radius = r
				}
			}

			info, ok := i.connections.Load(conn)
			if !ok || info.(ConnectionInfo).Section != "gowars" || info.(ConnectionInfo).Shipname == "" {
				return "You must be in GOWARS with a ship to use this command"
			}
			if radius < 0 || radius > 10 {
				return "Radius must be <= 10"
			}

			connInfo := info.(ConnectionInfo)
			senderSide := ""
			senderX, senderY := 0, 0

			for _, obj := range i.objects {
				if obj.Type == "Ship" && obj.Name == connInfo.Shipname && obj.Galaxy == connInfo.Galaxy {
					senderSide = obj.Side
					senderX = obj.LocationX
					senderY = obj.LocationY
					break
				}
			}

			if senderSide == "" {
				return "Could not determine your ship's location or side."
			}

			var targets []string
			for _, obj := range i.objects {
				if obj.Galaxy != connInfo.Galaxy {
					continue
				}
				if obj.Side == senderSide || obj.Side == "neutral" {
					continue
				}
				dist := math.Sqrt(math.Pow(float64(obj.LocationX-senderX), 2) + math.Pow(float64(obj.LocationY-senderY), 2))
				if int(dist) <= radius {
					targets = append(targets, fmt.Sprintf("%s (%s) at %d-%d [distance: %.1f]", obj.Name, obj.Type, obj.LocationX, obj.LocationY, dist))
				}
			}

			if len(targets) == 0 {
				return fmt.Sprintf("No targets found within %d sectors.", radius)
			}
			return fmt.Sprintf("Targets within %d sectors:\r\n%s", radius, strings.Join(targets, "\r\n"))
		},
		Help: "List information on TARGETS\r\n" +
			"Syntax: TArgets [<keywords>]\r\n" +
			"\r\n" +
			"Primarily for locating targets during battle, when a SCAN would be too\r\n" +
			"time consuming. List location and shield percent of any enemy ship,\r\n" +
			"base, or planet in range; name of any enemy ship in game (including\r\n" +
			"the Romulan); or location and number of builds of any known enemy\r\n" +
			"planet. TARGETS is equivalent to a LIST command with a default range\r\n" +
			"of 10 sectors and a default side of enemy.\r\n" +
			"\r\n" +
			"Examples:\r\n" +
			"TA                      List all targets within 10 sectors.\r\n" +
			"TA 10                   Equivalent to \"TA\".\r\n" +
			"TA 5                    List all targets within 5 sectors.",
	}

	i.gowarsCommands["time"] = Command{

		Handler: func(args []string, conn net.Conn) string {
			return i.pregameCommands["time"].Handler(args, conn)
		},
		Help: "List various TIMEs\r\n" +
			"Syntax: TIme\r\n" +
			"\r\n" +
			"List time since game started; time since your ship entered the game;\r\n" +
			"run time for your job so far this game; total run time since login;\r\n" +
			"and current time of day.",
	}

	// 	Torpedos parameters supported examples:
	//		Command		# torps Default		# parms		tested
	//		Tor 44 33	1	ICDEF		2		yes
	//		tor co j	1	Computed	2		yes
	//		tor 2 4 -1	2	ICDEF		3		yes
	//		tor r 0 -2 	1	Relative	3		yes
	//		tor a 50 55	1	absolute	3		Yes
	//		tor c 2 wolf	2	Computed	3		Yes
	//		tor a 33 55	1	absolute	3		Yes
	//		tor a 3 33 55	3	absolute	4		yes
	//		tor r 2 1 3	2	Relative	4		yes
	//		tor r 2 1       1       Relative        3               yes
	//
	i.gowarsCommands["torpedoes"] = Command{
		Handler: func(args []string, conn net.Conn) string {
			// Help text
			if len(args) == 0 || (len(args) == 1 && args[0] == "?") {
				return "torpedoes absolute <vpos> <hpos>\r\ntorpedoes relative <vpos> <hpos>\r\ntorpedoes computed <shipname>\r\ntorpedo [n] <vpos> <hpos>\r\ntorpedo <mode> <numtorps> <vpos> <hpos>"
			}

			// Get connection info for galaxy and ICdef
			info, ok := i.connections.Load(conn)
			if !ok {
				return "Error: connection not found"
			}
			connInfo := info.(ConnectionInfo)

			// Add abbreviation support for computed mode (e.g., 'c' for 'computed')
			if len(args) >= 1 {
				firstArg := strings.ToLower(args[0])
				if firstArg == "c" {
					args[0] = "computed"
				}
			}
			switch len(args) {
			case 2:
				return i.handleTorpedo2Args(args, conn, connInfo)
			case 3:
				return i.handleTorpedo3Args(args, conn, connInfo)
			case 4:
				return i.handleTorpedo4Args(args, conn, connInfo)
			default:
				return "Invalid syntax.\r\nSyntax:\r\nTOrpedo [numTorps]<vpos> <hpos>\r\nTOrpedo [Absolute|Relative] [numTorps]  <vpos> <hpos> \r\nTOrpedo Computed [numTorps] <shipname>\r\nTOrpedo <mode> <numTorps> <vpos> <hpos>"
			}
		},

		Help: "Fire photon TORPEDO burst\r\n" +
			"Syntax:\r\n" +
			"TOrpedo [Absolute|Relative|Computed] n <vpos><hpos> \r\n" +
			"\r\n" +
			"A photon torpedo is aimed along a path in physical space, thus any\r\n" +
			"object lying along its path will intercept the torpedo. One, two, or\r\n" +
			"three torpedoes may be fired with one command, and the torpedoes may\r\n" +
			"be individually targeted, or fired at a common location. The minimum\r\n" +
			"range of a torpedo is 8 sectors, but some will travel 10 sectors\r\n" +
			"before self-destructing. Torpedoes may be deflected from the desired\r\n" +
			"track by a number of different factors, including your ship's shield\r\n" +
			"strength, computer and torpedo tube damage, and torpedo misfires. A\r\n" +
			"torpedo misfire also aborts the remainder of the burst, and sometimes\r\n" +
			"damages the torpedo tubes as well. Torpedoes can cause stars to go\r\n" +
			"nova, and can also destroy planets (if no enemy installations remain\r\n" +
			"intact). \"Accidental\" hits on friendly ships, bases, or planets are\r\n" +
			"automatically neutralized. A torpedo burst uses no ship energy.\r\n" +
			"Firing torpedoes (or getting hit by one) puts you on red alert.\r\n" +
			"\r\n" +
			"Examples:\r\n" +
			"TO 1 12 24             Fire one torpedo at sector 12-24.\r\n" +
			"TO 3 12 24             Fire three torpedoes at sector 12-24.\r\n" +
			"TO A 3 12 24           Equivalent to \"TO 3 12 24\".\r\n" +
			"TO R 2 2 -5            Fire two torpedoes at sector 22-25, assuming your\r\n" +
			"                        location is 20-30.\r\n" +
			"TO C 3 BUZZARD         Fire three torpedoes at the Buzzard.\r\n" +
			"TO C 1 E               Fire one torpedo at the Excalibur.",
	}

	i.gowarsCommands["tractor"] = Command{
		Handler: func(args []string, conn net.Conn) string {
			// Turn tractor off
			if len(args) == 0 {
				return i.tractorOff(conn)
			}

			// Support: tractor <vpos> <hpos> only if DecwarMode == false (per-galaxy)
			if len(args) == 2 {
				galaxyDecwarMode := DecwarMode
				if info, ok := i.connections.Load(conn); ok {
					connGalaxy := info.(ConnectionInfo).Galaxy
					i.galaxyParamsMutex.RLock()
					if gp, gpOk := i.galaxyParams[connGalaxy]; gpOk {
						galaxyDecwarMode = gp.DecwarMode
					}
					i.galaxyParamsMutex.RUnlock()
				}
				if !galaxyDecwarMode {
					vpos, hpos, err := i.parseCoordinates(args[0], args[1], conn, false)
					if err != nil {
						return "Invalid coordinates: " + err.Error()
					}
					// Find object at those coordinates in the player's galaxy
					info, ok := i.connections.Load(conn)
					if !ok {
						return "Connection info not found"
					}
					connInfo := info.(ConnectionInfo)
					targetObj := i.getObjectAtLocation(connInfo.Galaxy, vpos, hpos)
					if targetObj != nil {
						obj := targetObj
						// Tractor stub logic as specified
						// Find my ship
						var myShip *Object
						for idx := range i.objects {
							if i.objects[idx].Type == "Ship" && i.objects[idx].Name == connInfo.Shipname && i.objects[idx].Galaxy == connInfo.Galaxy {
								myShip = i.objects[idx]
								break
							}
						}
						if myShip == nil {
							return "Error: your ship not found"
						}
						// 1. If my ship's tractor is on
						if myShip.TractorOnOff {
							return "Tractor beam already active, Captain"
						}
						// 2. If my ship's shields are up
						if myShip.ShieldsUpDown {
							return "Can not apply tractor beam through shields, Captain."
						}
						// 3. If the other object is not adjacent
						if (AbsInt(obj.LocationX-myShip.LocationX) > 1) || (AbsInt(obj.LocationY-myShip.LocationY) > 1) {
							return "Not adjacent to destination object."
						}
						// 4. If the object is my ship
						if obj.Name == myShip.Name && obj.Type == myShip.Type && obj.Galaxy == myShip.Galaxy {
							return "Beg your pardon, Captain you want to apply a tractor beam to your own ship?"
						}
						// 5. Otherwise, update tractor fields for both
						myShip.TractorOnOff = true
						myShip.TractorShip = obj.Name
						obj.TractorOnOff = true
						obj.TractorShip = myShip.Name
						outline := "Tractor beam activated on "
						switch obj.Type {
						case "Romulan":
							return outline + obj.Type
						case "Ship":
							return outline + obj.Name
						case "Base":
							return outline + obj.Type
						case "Planet":
							return outline + obj.Type
						case "Star":
							return outline + obj.Type
						case "Black Hole":
							return outline + obj.Type
						}
					}
					return "No object found at those coordinates"
				}
				// If DecwarMode == true, fall through to normal shipname/off logic
			}

			param := strings.ToLower(args[0])
			if strings.HasPrefix("off", param) {
				return i.tractorOff(conn)
			}

			// Must have specific ship name
			// Expand abbreviated ship name (like tell)
			var matches []string
			i.connections.Range(func(_, value interface{}) bool {
				info := value.(ConnectionInfo)
				if info.Shipname != "" && strings.HasPrefix(strings.ToLower(info.Shipname), param) {
					matches = append(matches, info.Shipname)
				}
				return true
			})

			// If the ship name is provided, establish tractor control
			if len(matches) == 1 {
				return i.tractorOn(conn, matches[0])
			} else if len(matches) > 1 {
				return "Error: ambiguous ship abbreviation, matches: " + strings.Join(matches, ", ")
			} else {
				return "Error: no ship matches abbreviation"
			}
		},
		Help: "TRACTOR beam\r\n" +
			"Syntax: TRactor <ship name> or TRactor Off\r\n" +
			"\r\n" +
			"Tow another ship of the same team. The two ships must be located in\r\n" +
			"adjacent sectors and both ships must have their shields lowered. Once\r\n" +
			"such a beam is applied, either ship can pull the other behind it using\r\n" +
			"warp or impulse engines. Energy consumption for the towing ship is 3\r\n" +
			"times the normal rate for movement with the shields down. The ship\r\n" +
			"being towed will end the move trailing the lead ship. If either ship\r\n" +
			"raises deflector shields, the tractor beam is automatically cut. The\r\n" +
			"tractor beam will also be broken if either ship is hit by a torpedo or\r\n" +
			"damaged by a nova.\r\n" +
			"\r\n" +
			"Examples:\r\n" +
			"TR                      Break any existing tractor beam.\r\n" +
			"TR OFF                  Equivalent to \"TR\".\r\n" +
			"TR B                    Apply tractor beam to the Buzzard.\r\n" +
			"TR <vpos> <hpos>        Apply tractor beam to the Buzzard.",
	}
	i.gowarsCommands["type"] = Command{
		Handler: func(args []string, conn net.Conn) string {
			validTypes := map[string]bool{
				"option": true,
				"output": true,
			}
			// Prompting and tab completion
			if len(args) == 0 || (len(args) == 1 && (args[0] == "?" || args[0] == "")) {
				return "type Option | Output"
			}
			if len(args) > 1 {
				return "Error: Only one parameter allowed. Usage: type Option | Output"
			}
			arg := strings.ToLower(args[0])
			// Tab completion for Option or Output
			if strings.HasSuffix(arg, "?") {
				return "type Option | Output"
			}
			// Abbreviation support
			var matches []string
			for k := range validTypes {
				if strings.HasPrefix(k, arg) {
					matches = append(matches, k)
				}
			}
			var result string
			if len(matches) == 1 {
				switch matches[0] {
				case "option":
					// Look up per-galaxy params for the current connection's galaxy
					var galaxyDecwarMode bool = DecwarMode
					var galaxyMaxRomulans int = MaxRomulans
					var galaxyMaxBlackHoles int = MaxBlackHoles
					if info, ok := i.connections.Load(conn); ok {
						connGalaxy := info.(ConnectionInfo).Galaxy
						i.galaxyParamsMutex.RLock()
						if gp, gpOk := i.galaxyParams[connGalaxy]; gpOk {
							galaxyDecwarMode = gp.DecwarMode
							galaxyMaxRomulans = gp.MaxRomulans
							galaxyMaxBlackHoles = gp.MaxBlackHoles
						}
						i.galaxyParamsMutex.RUnlock()
					}

					if galaxyDecwarMode {
						result = gowarVersionDW
					} else {
						result = gowarVersion
					}

					// Show custom galaxy size if available
					if info, ok := i.connections.Load(conn); ok {
						connInfo := info.(ConnectionInfo)
						i.trackerMutex.Lock()
						if tracker, exists := i.galaxyTracker[connInfo.Galaxy]; exists && tracker.MaxSizeX > 0 && tracker.MaxSizeY > 0 {
							result += fmt.Sprintf("Galaxy Size: %dx%d\r\n", tracker.MaxSizeX, tracker.MaxSizeY)
						} else {
							result += fmt.Sprintf("Galaxy Size: %dx%d\r\n", MaxSizeX, MaxSizeY)
						}
						i.trackerMutex.Unlock()
					}

					if galaxyMaxRomulans > 0 {
						result += "There are Romulans in this game.\r\n"
					} else {
						result += "Romulans are NOT in this game.\r\n"
					}
					if galaxyMaxBlackHoles == 0 {
						result += "Black holes are NOT in this game.\r\n"
					} else {
						result += "There are Black holes in this game.\r\n"
					}
					if galaxyDecwarMode {
						result += "Game intelligence mode: Decwar (Fog of war mode)"
					} else {
						result += "Game intelligence mode: Gowar (Real time mode)"
					}
					return result
				case "output":
					// Print current output switch settings for this connection
					info, ok := i.connections.Load(conn)
					result := "Current output switch settings:\r\n\n"
					if ok {
						connInfo := info.(ConnectionInfo)
						switch connInfo.OutputState {
						case "short":
							result += "Short output format."
						case "medium":
							result += "Medium output format."
						case "long":
							result += "Long output format."
						default:
							result += "Unknown output format."
						}
						// Add promptOptions line
						switch strings.ToLower(connInfo.Prompt) {
						case "normal", "":
							result += "\r\nNormal command prompt."
						case "informative":
							result += "\r\nInformative command prompt."
						}
						// Add SCAN format line
						switch connInfo.Scan {
						case "short":
							result += "\r\nShort SCAN format."
						case "long":
							result += "\r\nLong SCAN format."
						}
						// Add ICdef line
						switch strings.ToLower(connInfo.ICdef) {
						case "relative", "":
							result += "\r\nRelative coordinates are default for input."
						case "absolute":
							result += "\r\nAbsolute coordinates are default for input."
						}
						// Add OCdef line
						switch strings.ToLower(connInfo.OCdef) {
						case "absolute":
							result += "\r\nAbsolute coordinates are default for output."
						case "relative":
							result += "\r\nRelative coordinates are default for output."
						case "both":
							result += "\r\nBoth coordinates are default for output."
						}
					} else {
						result += "Unknown output format."
					}
					// Add terminal type line
					result += "\r\nTerminal type:  Telnet"
					return result
				}
			} else if len(matches) > 1 {
				return "Ambiguous: type Option | Output"
			}
			return "Error: Parameter must be Option or Output"
		},
		Help: "TYPE game, input, and output settings\r\n" +
			"Syntax: TYpe OPtion|OUtput\r\n" +
			"\r\n" +
			"Type the current game OPTION and OUTPUT settings.\r\n" +
			"The OPTION settings are:\r\n" +
			"- The version number and date of implementation,\r\n" +
			"- Whether there are Romulans in the game,\r\n" +
			"- and whether there are Black Holes in the game.\r\n" +
			"The OUTPUT settings are:\r\n" +
			"- SHORT, MEDIUM, or LONG output,\r\n" +
			"- NORMAL or INFORMATIVE command prompt,\r\n" +
			"- SHORT or LONG sensor scans,\r\n" +
			"- ABSOLUTE or RELATIVE default for coordinate input,\r\n" +
			"- ABSOLUTE, RELATIVE, or BOTH for coordinate output,\r\n" +
			"- and the current TTYTYPE.\r\n" +
			"\r\n" +
			"Examples:\r\n" +
			"TY OP                   List the option settings.\r\n" +
			"TY OU                   List the output settings.",
	}

	// Add set to pregame commands
	i.pregameCommands["set"] = i.gowarsCommands["set"]

	// Add tell to pregame commands
	i.pregameCommands["tell"] = i.gowarsCommands["tell"]
}

// writeBaudf simulates baud rate by delaying character output
func (i *Interpreter) writeBaudf(conn net.Conn, writer *bufio.Writer, format string, a ...interface{}) {
	i.writeBaudfCtx(context.Background(), conn, writer, format, a...)
}

func (i *Interpreter) writeBaudfCtx(ctx context.Context, conn net.Conn, writer *bufio.Writer, format string, a ...interface{}) {
	// Get the writer mutex for this connection
	mutexRaw, ok := i.writerMutexs.Load(conn)
	if !ok {
		return // Connection not found, skip writing
	}
	mutex := mutexRaw.(*sync.Mutex)
	text := fmt.Sprintf(format, a...)
	var baudRate int
	if info, ok := i.connections.Load(conn); ok {
		baudRate = info.(ConnectionInfo).BaudRate
	} else {
		baudRate = 300 // Default if not found
	}

	// Lock the writer for the entire operation
	mutex.Lock()
	defer mutex.Unlock()

	if baudRate == 0 {
		// No baud rate simulation - output immediately
		select {
		case <-ctx.Done():
			// Only print [Output interrupted] once per stacked command batch
			if printedPtr, ok := ctx.Value("interruptedPrinted").(*bool); ok {
				if !*printedPtr {
					writer.WriteString("\r\n[Output interrupted]\r\n")
					*printedPtr = true
				}
			} else {
				writer.WriteString("\r\n[Output interrupted]\r\n")
			}
			prompt := i.getPrompt(conn)
			writer.WriteString(prompt)
			writer.Flush()
			return
		default:
		}
		writer.WriteString(text)
		writer.Flush()
		return
	}

	if baudRate < 0 {
		baudRate = 300 // Fallback to default
	}

	// 10 bits per character (8 data, 1 start, 1 stop)
	// delay per character = 10 / baudRate seconds
	//	delay := time.Duration(10*1000*1000*1000/baudRate) * time.Nanosecond
	delayNs := (int64(10) * 1000000000) / int64(baudRate)
	// Write characters in batches of 10 for better performance
	const batchSize = 10
	chars := []rune(text)

	for idx := 0; idx < len(chars); idx += batchSize {
		// Check if context is cancelled before each batch
		select {
		case <-ctx.Done():
			// Context cancelled, stop output immediately
			if printedPtr, ok := ctx.Value("interruptedPrinted").(*bool); ok {
				if !*printedPtr {
					writer.WriteString("\r\n[Output interrupted]\r\n")
					*printedPtr = true
				}
			} else {
				writer.WriteString("\r\n[Output interrupted]\r\n")
			}
			writer.Flush()
			prompt := i.getPrompt(conn)
			writer.WriteString(prompt)
			writer.Flush()
			return
		default:
		}

		// Write batch of characters
		end := idx + batchSize
		if end > len(chars) {
			end = len(chars)
		}

		for j := idx; j < end; j++ {
			writer.WriteRune(chars[j])
		}
		writer.Flush()

		// Calculate and apply delay for this batch
		batchDelayNs := delayNs * int64(end-idx)
		totalDelay := time.Duration(batchDelayNs) * time.Nanosecond

		// Create a single timer for the full duration
		timer := time.NewTimer(totalDelay)

		select {
		case <-ctx.Done():
			// Important: Stop the timer if we exit early to clean up immediately
			timer.Stop()

			// Context cancelled during delay
			if printedPtr, ok := ctx.Value("interruptedPrinted").(*bool); ok {
				if !*printedPtr {
					writer.WriteString("\r\n[Output interrupted]\r\n")
					*printedPtr = true
				}
			} else {
				writer.WriteString("\r\n[Output interrupted]\r\n")
			}
			writer.Flush()
			prompt := i.getPrompt(conn)
			writer.WriteString(prompt)
			writer.Flush()
			return
		case <-timer.C:
			// The delay finished naturally
		}
	}
}

// contains checks if a slice contains a string
func (i *Interpreter) handleStatus(args []string, conn net.Conn) string {
	return i.handleStatusCtx(context.Background(), args, conn)
}

func (i *Interpreter) handleStatusCtx(ctx context.Context, args []string, conn net.Conn) string {
	// Parameters and their shortest unique abbreviations
	statusParams := []string{
		"Condition",
		"Location",
		"Torpedoes",
		"Energy",
		"Damage",
		"Shields",
		"Radio",
	}
	statusmedParams := []string{
		"Cond",
		"Loc",
		"Torps",
		"Ener",
		"Dam",
		"Shlds",
		"Rad",
	}
	statusshParams := []string{
		"C",
		"L",
		"T",
		"E",
		"D",
		"S",
		"R",
	}

	statusParamAbbrevs := map[string]string{
		"Condition": "C",
		"Location":  "L",
		"Torpedoes": "T",
		"Energy":    "E",
		"Damage":    "D",
		"Shields":   "S",
		"Radio":     "R",
	}

	var outputOption string
	var filteredArgs []string
	// Default to OutputState from connection, unless overridden by explicit output parameter
	if info, ok := i.connections.Load(conn); ok {
		connInfo := info.(ConnectionInfo)
		switch connInfo.OutputState {
		case "medium", "short":
			outputOption = connInfo.OutputState
		default:
			outputOption = "long"
		}
	} else {
		outputOption = "long"
	}
	for i := 0; i < len(args); i++ {
		arg := args[i]
		if strings.ToLower(arg) == "output" && i+1 < len(args) {
			val := strings.ToLower(args[i+1])
			if val == "long" || val == "medium" || val == "short" {
				outputOption = val
				i++ // skip value
				continue
			}
		}
		filteredArgs = append(filteredArgs, arg)
	}

	// Tab completion: if argument ends with '?', suggest completions
	for _, arg := range filteredArgs {
		if strings.HasSuffix(arg, "?") {
			prefix := strings.ToLower(strings.TrimSuffix(arg, "?"))
			matches := []string{}
			for _, param := range statusParams {
				abbr := strings.ToLower(statusParamAbbrevs[param])
				if strings.HasPrefix(strings.ToLower(param), prefix) || strings.HasPrefix(abbr, prefix) {
					matches = append(matches, param)
				}
			}
			if len(matches) == 0 {
				return "Error: No valid completion for parameter"
			}
			return "status " + strings.Join(matches, " | ")
		}
	}

	// If no parameters, show all (based on output format)
	if info, ok := i.connections.Load(conn); ok {
		connInfo := info.(ConnectionInfo)

		if len(filteredArgs) == 0 {
			if connInfo.OutputState == "long" {
				return i.statusOutputCtx(ctx, statusParams, conn, outputOption)
			} else {
				if connInfo.OutputState == "medium" {
					return i.statusOutputCtx(ctx, statusmedParams, conn, outputOption)
				} else {
					return i.statusOutputCtx(ctx, statusshParams, conn, outputOption)
				}
			}
		}
	}
	// Resolve each parameter (abbreviation or full)
	var resolved []string
	for _, arg := range filteredArgs {
		input := strings.ToLower(arg)
		var matches []string
		for _, param := range statusParams {
			abbr := strings.ToLower(statusParamAbbrevs[param])
			if strings.HasPrefix(strings.ToLower(param), input) || strings.HasPrefix(abbr, input) {
				matches = append(matches, param)
			}
		}
		if len(matches) == 1 {
			resolved = append(resolved, matches[0])
		} else if len(matches) == 0 {
			return fmt.Sprintf("Error: Unknown status parameter '%s'.", arg)
		} else {
			return fmt.Sprintf("Error: Ambiguous parameter '%s'. Matches: %s", arg, strings.Join(matches, ", "))
		}
	}

	return i.statusOutputCtx(ctx, resolved, conn, outputOption)
}

// Function for status

func (i *Interpreter) statusOutputCtx(ctx context.Context, params []string, conn net.Conn, outputOptions ...string) string {
	var sb strings.Builder
	var savedShields int
	shieldudflag := "-"
	// Add stardate line for user's ship
	starDateStr := ""

	if info, ok := i.connections.Load(conn); ok {
		connInfo := info.(ConnectionInfo)
		if connInfo.Ship != nil {
			ship := connInfo.Ship
			if connInfo.OutputState == "long" || connInfo.OutputState == "medium" {
				starDateStr = fmt.Sprintf("Stardate \t%d\r\n", ship.StarDate)
			} else {
				starDateStr = fmt.Sprintf("SD%d ", ship.StarDate)
			}
		}
	}
	sb.WriteString(starDateStr)

	for _, param := range params {
		// Check for context cancellation during status parameter processing
		select {
		case <-ctx.Done():
			return "[Output interrupted]"
		default:
		}
		if param == "Location" || param == "Loc" || param == "L" {
			var x, y int
			//			var ok bool
			if info, okConn := i.connections.Load(conn); okConn {
				connInfo := info.(ConnectionInfo)
				if connInfo.AdminMode {
					// Use ICdef for admin
					if connInfo.ICdef == "relative" && connInfo.Ship != nil {
						x = connInfo.Ship.LocationX
						y = connInfo.Ship.LocationY
					} else if connInfo.ICdef == "absolute" && connInfo.Ship != nil {
						x = connInfo.Ship.LocationX
						y = connInfo.Ship.LocationY
					} else if connInfo.Ship != nil {
						x = connInfo.Ship.LocationX
						y = connInfo.Ship.LocationY
					}
				} else {
					x, y, _ = i.getShipLocation(conn)
				}
			}
			if param == "Location" {
				sb.WriteString(fmt.Sprintf("Location \t%d-%d\r\n", x, y))
			} else {
				if param == "Loc" {
					sb.WriteString(fmt.Sprintf("Loc \t\t%d-%d\r\n", x, y))
				} else { //must be short
					sb.WriteString(fmt.Sprintf(" %d-%d", x, y))
				}
			}
		} else if param == "Condition" || param == "Cond" || param == "C" {
			condition := "<unknown>"
			if info, ok := i.connections.Load(conn); ok {
				connInfo := info.(ConnectionInfo)
				if connInfo.Ship != nil {
					condition = connInfo.Ship.Condition
				}
			}
			if param == "Condition" {
				sb.WriteString(fmt.Sprintf("Condition \t%s\r\n", condition))
			} else {
				if param == "Cond" {
					sb.WriteString(fmt.Sprintf("Cond \t\t%s\r\n", condition))
				} else { // must be short
					sb.WriteString(fmt.Sprintf(" %c", condition[0]))
				}
			}
		} else if param == "Torpedoes" || param == "Torps" || param == "T" {
			torpedoes := "<unknown>"
			if info, ok := i.connections.Load(conn); ok {
				connInfo := info.(ConnectionInfo)
				if connInfo.Ship != nil {
					torpedoes = fmt.Sprintf("%d", connInfo.Ship.TorpedoTubes)
				}
			}
			if param == "Torpedoes" {
				sb.WriteString(fmt.Sprintf("Torpedoes \t%s\r\n", torpedoes))
			} else {
				if param == "Torps" {
					sb.WriteString(fmt.Sprintf("Torps \t\t%s\r\n", torpedoes))
				} else {
					sb.WriteString(fmt.Sprintf(" T%s", torpedoes))
				}
			}
		} else if param == "Energy" || param == "Ener" || param == "E" {
			energy := "<unknown>"
			var numEnergy int
			if info, ok := i.connections.Load(conn); ok {
				connInfo := info.(ConnectionInfo)
				if connInfo.Ship != nil {
					energy = fmt.Sprintf("        %.1f", float64(connInfo.Ship.ShipEnergy)/10.0)
					numEnergy = connInfo.Ship.ShipEnergy / 10
				}
			}
			if param == "Energy" {
				sb.WriteString(fmt.Sprintf("Energy \t%s\r\n", energy))
			} else {
				if param == "Ener" {
					sb.WriteString(fmt.Sprintf("Ener \t%s\r\n", energy))
				} else {
					sb.WriteString(fmt.Sprintf(" E%d", numEnergy)) //short
				}
			}
		} else if param == "Shields" || param == "Shlds" || param == "S" {
			shields := "<unknown>"
			if info, ok := i.connections.Load(conn); ok {
				connInfo := info.(ConnectionInfo)
				if connInfo.Ship != nil {
					ship := connInfo.Ship
					shieldPct := float64(ship.Shields) / float64(InitialShieldValue) * 100.0
					shieldStr := fmt.Sprintf("%.0f%%", float64(shieldPct))
					if ship.ShieldsUpDown == true {
						shieldudflag = "+"
					}
					shieldStr = shieldudflag + shieldStr

					shields = shieldStr + " " + fmt.Sprintf("%.1f", float64(ship.Shields)/10.0)
					savedShields = ship.Shields
				}
			}
			if param == "Shields" {
				sb.WriteString(fmt.Sprintf("Shields \t%s units\r\n", shields))
			} else {
				if param == "Shlds" {
					sb.WriteString(fmt.Sprintf("Shlds \t\t%s units\r\n", shields))
				} else { //short
					sb.WriteString(fmt.Sprintf(" SH%s%d", shieldudflag, savedShields/InitialShieldValue*100)) //short
				}
			}
		} else if param == "Radio" || param == "Rad" || param == "R" {
			radio := "<unknown>"
			if info, ok := i.connections.Load(conn); ok {
				connInfo := info.(ConnectionInfo)
				if connInfo.Ship != nil {
					if connInfo.Ship.RadioOnOff {
						radio = "On"
					} else {
						radio = "Off"
					}
				}
			}
			if param == "Radio" {
				sb.WriteString(fmt.Sprintf("Radio \t\t%s\r\n", radio))
			} else {
				if param == "Rad" {
					sb.WriteString(fmt.Sprintf("Radio \t\t%s\r\n", radio))
				} else {
					sb.WriteString(fmt.Sprintf(" R%s", radio))
				}
			}
		} else if param == "Damage" || param == "Dam" || param == "D" {
			if info, ok := i.connections.Load(conn); ok {
				connInfo := info.(ConnectionInfo)
				totdam := 0
				if connInfo.Ship != nil {

					totdam = connInfo.Ship.TotalShipDamage

				}
				if param == "Damage" {
					sb.WriteString(fmt.Sprintf("Damage \t\t%.1f\r\n", float64(totdam)/100.0))
				} else {
					if param == "Dam" {
						sb.WriteString(fmt.Sprintf("Dam \t\t%.1f\r\n", float64(totdam)/100.0))
					} else {
						sb.WriteString(fmt.Sprintf(" D%.1f", float64(totdam)/100.0))
					}
				}
			}
		}
	}
	return sb.String()
}

func (i *Interpreter) parseCoordinates(xStr, yStr string, conn net.Conn, forceAbsolute bool) (int, int, error) {
	info, ok := i.connections.Load(conn)
	if !ok {
		return 0, 0, fmt.Errorf("connection not found")
	}
	connInfo := info.(ConnectionInfo)

	// Parse the coordinate strings as integers
	x, err := strconv.Atoi(xStr)
	if err != nil {
		return 0, 0, fmt.Errorf("invalid x coordinate: %s", xStr)
	}
	y, err := strconv.Atoi(yStr)
	if err != nil {
		return 0, 0, fmt.Errorf("invalid y coordinate: %s", yStr)
	}

	// If ICdef is relative, add current ship position to the parsed coordinates
	if !forceAbsolute && connInfo.ICdef == "relative" {
		shipX, shipY, ok := i.getShipLocation(conn)
		if !ok {
			return 0, 0, fmt.Errorf("unable to determine ship location for relative coordinates")
		}
		x += shipX
		y += shipY
	}

	return x, y, nil
}

func contains(slice []string, item string) bool {
	for _, s := range slice {
		if s == item {
			return true
		}
	}
	return false
}

// resolveParameter resolves an abbreviated parameter to its full form
func (i *Interpreter) resolveParameter(input string, validOptions map[string]bool) (string, bool) {
	input = strings.ToLower(input)
	var matches []string
	for opt := range validOptions {
		if strings.HasPrefix(strings.ToLower(opt), input) {
			matches = append(matches, opt)
		}
	}
	if len(matches) == 1 {
		return matches[0], true
	}
	return "", false // Return false if no match or ambiguous
}

// getCompletions provides command or parameter suggestions based on section and input
func (i *Interpreter) getCompletions(input string, section string, conn net.Conn) []string {
	// Enhanced handling for any command abbreviation + '?', with or without space before '?'
	trimmed := strings.TrimSpace(input)
	// Remove any space before '?'
	if strings.HasSuffix(trimmed, "?") {
		withoutQ := strings.TrimSuffix(trimmed, "?")
		withoutQ = strings.TrimSpace(withoutQ)
		parts := strings.Fields(withoutQ)
		if len(parts) == 1 {
			prefix := strings.ToLower(parts[0])
			commands := i.pregameCommands
			if section == "gowars" {
				commands = i.gowarsCommands
			}
			fullCmd, ok := i.resolveCommand(prefix, section)
			if ok {
				// Only one match, so auto-complete
				return []string{fullCmd}
			} else {
				// Multiple matches, show all
				var completions []string
				for cmd := range commands {
					if strings.HasPrefix(cmd, prefix) {
						completions = append(completions, cmd)
					}
				}
				sort.Strings(completions)
				return completions
			}
		}
	}
	input = strings.TrimRight(input, "?") // Remove trailing ? for processing
	parts := strings.Fields(input)
	commands := i.pregameCommands
	if section == "gowars" {
		commands = i.gowarsCommands
	}

	// Special case for 'type' and 'summary' commands
	if len(parts) >= 1 {
		cmd := strings.ToLower(parts[0])
		fullCmd, ok := i.resolveCommand(cmd, section)
		if ok {
			if fullCmd == "type" {
				typeParams := []string{"Option", "Output"}
				if len(parts) == 1 && (strings.HasSuffix(input, "?") || strings.HasSuffix(input, " ")) {
					return typeParams
				}
				if len(parts) == 2 {
					prefix := strings.ToLower(strings.TrimSuffix(parts[1], "?"))
					var matches []string
					for _, param := range typeParams {
						if strings.HasPrefix(strings.ToLower(param), prefix) {
							matches = append(matches, param)
						}
					}
					if len(matches) == 1 {
						return []string{fmt.Sprintf("type %s", matches[0])}
					}
					if len(matches) > 1 {
						return matches
					}
					return typeParams
				}
			} else if fullCmd == "summary" && section == "pregame" {
				params := []string{"all", "list"}
				if len(parts) == 1 && (strings.HasSuffix(input, "?") || strings.HasSuffix(input, " ")) {
					return append(params, "<galaxy_number>")
				}
				if len(parts) == 2 {
					prefix := strings.ToLower(strings.TrimSuffix(parts[1], "?"))
					var matches []string
					for _, param := range params {
						if strings.HasPrefix(strings.ToLower(param), prefix) {
							matches = append(matches, param)
						}
					}
					if len(matches) == 1 {
						return []string{fmt.Sprintf("summary %s", matches[0])}
					}
					if len(matches) > 1 {
						return matches
					}
					return append(params, "<galaxy_number>")
				}
			}
		}
	}

	// Command completion - but skip if we have an exact match and want parameter completion
	if len(parts) == 1 && !strings.HasSuffix(input, " ") {
		prefix := strings.ToLower(parts[0])
		// Check if this is an exact command match - if so, fall through to parameter completion
		if _, exists := commands[prefix]; !exists {
			var completions []string
			for cmd := range commands {
				if strings.HasPrefix(cmd, prefix) {
					completions = append(completions, cmd)
				}
			}
			sort.Strings(completions)
			return completions
		}
		// Exact match found - continue to parameter completion below
	}

	// If only command and a space, prompt for parameters for any unique command
	if len(parts) == 1 && strings.HasSuffix(input, " ") {
		cmd := strings.ToLower(parts[0])
		fullCmd, ok := i.resolveCommand(cmd, section)
		if ok {
			switch fullCmd {
			case "scan":
				return []string{"scan up", "scan down", "scan right", "scan left", "scan corner", "scan warn", "scan <radius>", "scan <vpos> <hpos>"}
			case "summary":
				if section == "pregame" {
					return []string{"summary all", "summary <galaxy_number>"}
				}
			case "list":
				return []string{"list neutral", "list friendly", "list enemy", "list closest", "list ships", "list bases", "list planets", "list summary", "list ports", "list captured", "list <radius>"}
			case "build":
				return []string{
					"build relative <vpos> <hpos>",
					"build absolute <vpos> <hpos>",
					"build <vpos> <hpos>",
				}
			case "targets":
				params := []string{"ships", "bases", "planets", "all", "romulan", "closest", "list", "summary", "<radius>"}
				var completions []string
				for _, param := range params {
					completions = append(completions, "targets "+param)
				}
				return completions
			case "bases":
				return []string{"bases", "bases enemy", "bases sum", "bases all", "bases closest", "bases <vpos> <hpos>"}
			case "status":
				statusParams := []string{"Condition", "Location", "Torpedoes", "Energy", "Damage", "Shields", "Radio"}
				var completions []string
				for _, param := range statusParams {
					completions = append(completions, "status "+param)
				}
				return completions
			case "damages":
				damagesParams := []string{"Warp", "Shields", "Phaser", "Computer", "Life", "Radio", "Ship", "Tractor", "Impulse"}
				var completions []string
				for _, param := range damagesParams {
					completions = append(completions, "damages "+param)
				}
				return completions
			case "tell":
				var completions []string
				info, ok := i.connections.Load(conn)
				if ok {
					connInfo := info.(ConnectionInfo)

					if connInfo.Section == "gowars" {
						// In gowars mode: show optional parameters and shipnames, but NOT connections
						params := []string{"all", "federation", "human", "empire", "klingon", "enemy", "friendly"}
						for _, param := range params {
							completions = append(completions, "tell "+param)
						}

						// Add active shipnames from user's current galaxy
						userGalaxy := connInfo.Galaxy
						i.connections.Range(func(_, value interface{}) bool {
							info := value.(ConnectionInfo)
							if info.Section == "gowars" && info.Shipname != "" && info.Galaxy == userGalaxy {
								completions = append(completions, "tell "+info.Shipname)
							}
							return true
						})
					} else {
						// In pregame mode: show connections only (usernames)
						i.connections.Range(func(_, value interface{}) bool {
							info := value.(ConnectionInfo)
							if info.Name != "" {
								completions = append(completions, "tell "+info.Name)
							}
							if info.Port != "" {
								completions = append(completions, "tell "+info.Port)
							}
							return true
						})
					}
				}
				sort.Strings(completions)
				return completions
			case "planets":
				return []string{"planets", "planets sum", "planets all"}
			case "radio":
				return []string{"radio on", "radio off"}
			case "shields":
				return []string{"shields up", "shields down", "shields transfer"}
			case "capture":
				return []string{
					"capture relative <vpos> <hpos>",
					"capture absolute <vpos> <hpos>",
					"capture <vpos> <hpos>",
				}
			case "phasers":
				return []string{"phasers absolute <vpos> <hpos>", "phasers relative <vpos> <hpos>", "phasers computed <shipname>"}
			case "torpedoes":
				return []string{"torpedoes absolute <vpos> <hpos>", "torpedoes relative <vpos> <hpos>", "torpedoes computed <shipname>"}
			case "admin":
				adminParams := []string{"ShieldsDamage", "WarpDamage", "ImpulseDamage", "LifeSupport", "TorpDamage", "PhaserDamage", "ComputerDamage", "RadioDamage", "TractorDamage", "ShieldEnergy", "ShipEnergy", "NumTorps", "Password", "Create", "Beam", "Status", "Damages", "Runtime", "ShipDamage"}
				var completions []string
				for _, param := range adminParams {
					completions = append(completions, "admin "+param)
				}
				return completions
			}
		}
	}

	// Parameter completion for build command abbreviations (e.g., build r <tab>)
	if len(parts) == 2 {
		cmd := strings.ToLower(parts[0])
		fullCmd, ok := i.resolveCommand(cmd, section)
		if ok && fullCmd == "build" {
			// Abbreviation support for parameters
			validParams := map[string]bool{"relative": true, "absolute": true}
			if resolved, ok := i.resolveParameter(strings.ToLower(parts[1]), validParams); ok {
				return []string{fmt.Sprintf("build %s ", resolved)}
			}
			// If ambiguous or no match, show all options
			return []string{
				"build relative <vpos> <hpos>",
				"build absolute <vpos> <hpos>",
				"build <vpos> <hpos>",
			}
		}
	}

	// Parameter completion for capture command abbreviations (e.g., cap r <tab>)
	if len(parts) == 2 {
		cmd := strings.ToLower(parts[0])
		fullCmd, ok := i.resolveCommand(cmd, section)
		if ok && fullCmd == "capture" {
			// Abbreviation support for parameters
			validParams := map[string]bool{"relative": true, "absolute": true}
			if resolved, ok := i.resolveParameter(strings.ToLower(parts[1]), validParams); ok {
				return []string{fmt.Sprintf("capture %s ", resolved)}
			}
			// If ambiguous or no match, show both options
			return []string{
				"capture relative <vpos> <hpos>",
				"capture absolute <vpos> <hpos>",
			}
		}
	}

	// Parameter completion
	if len(parts) == 0 {
		// Defensive: no command to complete, return empty slice
		return []string{}
	}
	cmd := strings.ToLower(parts[0])
	fullCmd, ok := i.resolveCommand(cmd, section)
	if !ok {
		return []string{"Invalid command: " + cmd}
	}

	// Enhanced shields parameter completion for abbreviations (e.g., sh tr, shields tr)
	if fullCmd == "shields" || cmd == "sh" {
		shieldsParams := []string{"up", "down", "transfer"}
		// If entering a parameter, suggest completions for it (abbreviation support)
		if len(parts) == 2 {
			abbr := strings.ToLower(parts[1])
			var matches []string
			for _, param := range shieldsParams {
				if strings.HasPrefix(param, abbr) {
					matches = append(matches, param)
				}
			}
			if len(matches) == 1 {
				if matches[0] == "transfer" {
					return []string{fmt.Sprintf("%s transfer <value>", fullCmd)}
				}
				return []string{fmt.Sprintf("%s %s", fullCmd, matches[0])}
			} else if len(matches) > 1 {
				var completions []string
				for _, m := range matches {
					if m == "transfer" {
						completions = append(completions, fmt.Sprintf("%s transfer <value>", fullCmd))
					} else {
						completions = append(completions, fmt.Sprintf("%s %s", fullCmd, m))
					}
				}
				return completions
			} else {
				// If no match, show all options
				return []string{"shields up", "shields down", "shields transfer"}
			}
		}
		// If user types "shields transfer ?" or "sh tr ?", prompt for value
		if len(parts) == 3 && (strings.ToLower(parts[1]) == "transfer" || strings.ToLower(parts[1]) == "tr") && (parts[2] == "?" || strings.HasSuffix(parts[2], "?")) {
			return []string{"shields transfer <value>"}
		}
	}

	// Support abbreviations for move (mo), scan (sc), list (li), status (st)
	// If command is abbreviated and followed by "?", show parameter prompts
	if (cmd == "mo" || fullCmd == "move") && (len(parts) == 2 && parts[1] == "?") {
		// Abbreviation completion for move command parameters
		moveParams := []string{"absolute", "relative", "computed"}
		if len(parts) == 2 {
			abbr := strings.ToLower(parts[1])
			matches := []string{}
			for _, param := range moveParams {
				if strings.HasPrefix(param, abbr) {
					matches = append(matches, param)
				}
			}
			if len(matches) == 1 {
				if matches[0] == "computed" {
					return []string{fmt.Sprintf("%s computed", fullCmd)}
				}
				return []string{fmt.Sprintf("%s %s <vpos> <hpos>", fullCmd, matches[0])}
			} else if len(matches) > 1 {
				return matches
			} else {
				return moveParams
			}
		}
	}

	// Support abbreviations for impulse (im)
	// If command is abbreviated and followed by "?", show parameter prompts
	if (cmd == "im" || fullCmd == "impulse") && (len(parts) == 2 && parts[1] == "?") {
		// Abbreviation completion for move command parameters
		moveParams := []string{"absolute", "relative", "computed"}
		if len(parts) == 2 {
			abbr := strings.ToLower(parts[1])
			matches := []string{}
			for _, param := range moveParams {
				if strings.HasPrefix(param, abbr) {
					matches = append(matches, param)
				}
			}
			if len(matches) == 1 {
				if matches[0] == "computed" {
					return []string{fmt.Sprintf("%s computed", fullCmd)}
				}
				return []string{fmt.Sprintf("%s %s <vpos> <hpos>", fullCmd, matches[0])}
			} else if len(matches) > 1 {
				return matches
			} else {
				return moveParams
			}
		}
	}

	// Support abbreviations for phasers (ph, phas) - only when second part is "?"
	if (cmd == "ph" || cmd == "phas" || fullCmd == "phasers") && (len(parts) == 2 && parts[1] == "?") {
		// Abbreviation completion for phasers command parameters
		phaserParams := []string{"absolute", "relative", "computed"}
		if len(parts) == 2 {
			abbr := strings.ToLower(parts[1])
			matches := []string{}
			for _, param := range phaserParams {
				if strings.HasPrefix(param, abbr) {
					matches = append(matches, param)
				}
			}
			if len(matches) == 1 {
				return []string{fmt.Sprintf("%s %s", fullCmd, matches[0])}
			} else if len(matches) > 1 {
				return matches
			} else {
				return phaserParams
			}
		}
	}

	// Support abbreviations for torpedoes (to)
	// If command is abbreviated and followed by "?", show parameter prompts
	if (cmd == "to" || fullCmd == "torpedoes") && (len(parts) == 2 && parts[1] == "?") {
		// Abbreviation completion for torpedoes command parameters
		torpedoParams := []string{"absolute", "relative", "computed"}
		if len(parts) == 2 {
			abbr := strings.ToLower(parts[1])
			matches := []string{}
			for _, param := range torpedoParams {
				if strings.HasPrefix(param, abbr) {
					matches = append(matches, param)
				}
			}
			if len(matches) == 1 {
				return []string{fmt.Sprintf("%s %s", fullCmd, matches[0])}
			} else if len(matches) > 1 {
				return matches
			} else {
				return torpedoParams
			}
		}
	}

	// Abbreviation completion for status command parameters (multiple parameters supported)
	if (cmd == "st" || fullCmd == "status") && len(parts) > 1 {
		statusParams := []string{"Condition", "Location", "Torpedoes", "Energy", "Damage", "Shields", "Radio"}
		var completedParams []string
		var ambiguousParams [][]string
		for i := 1; i < len(parts); i++ {
			abbr := strings.ToLower(parts[i])
			matches := []string{}
			for _, param := range statusParams {
				if strings.HasPrefix(strings.ToLower(param), abbr) {
					matches = append(matches, param)
				}
			}
			if len(matches) == 1 {
				completedParams = append(completedParams, matches[0])
			} else if len(matches) > 1 {
				ambiguousParams = append(ambiguousParams, matches)
				completedParams = append(completedParams, parts[i]) // keep original for ambiguous
			} else {
				ambiguousParams = append(ambiguousParams, statusParams)
				completedParams = append(completedParams, parts[i]) // keep original for no match
			}
		}
		// If all parameters are unambiguous, return the completed command line
		if len(ambiguousParams) == 0 {
			return []string{fmt.Sprintf("%s %s", fullCmd, strings.Join(completedParams, " "))}
		} else {
			// If any ambiguous or unmatched, show all possible completions for those parameters
			var completions []string
			for _, params := range ambiguousParams {
				completions = append(completions, params...)
			}
			return completions
		}
	}

	// Completion for 'tractor' command: prompt <vpos> <hpos> if DecwarMode is false
	if fullCmd == "tractor" {
		// If only 'tractor' and a space, prompt for <vpos> <hpos> if DecwarMode == false
		if len(parts) == 1 && strings.HasSuffix(input, " ") {
			if !DecwarMode {
				return []string{"tractor <vpos> <hpos>", "tractor <shipname>", "tractor off"}
			} else {
				return []string{"tractor <shipname>", "tractor off"}
			}
		}
		// If user types 'tractor o', 'tractor of', or 'tractor o?'
		if len(parts) == 2 {
			param := strings.ToLower(strings.TrimSuffix(parts[1], "?"))
			if param == "o" || param == "of" || param == "off" {
				return []string{"tractor off"}
			}
			if strings.HasPrefix("off", param) {
				return []string{"tractor off"}
			}
			// Tab-completion for tractor <abbrev> to expand to full shipname(s)
			// Only if not 'off'
			prefix := param
			var completions []string
			i.connections.Range(func(_, value interface{}) bool {
				info := value.(ConnectionInfo)
				if info.Shipname != "" && strings.HasPrefix(strings.ToLower(info.Shipname), prefix) {
					completions = append(completions, "tractor "+info.Shipname)
				}
				return true
			})
			if !DecwarMode && param != "" {
				completions = append(completions, "tractor <vpos> <hpos>")
			}
			if len(completions) > 0 {
				return completions
			}
		}
		// If user types 'tractor o' and presses tab or '?', or 'tractor of'
		if len(parts) == 2 && (parts[1] == "?" || strings.HasSuffix(parts[1], "?")) {
			return []string{"tractor off"}
		}
	}

	// Support abbreviations for move (mo), scan (sc), list (li)
	// If command is abbreviated and followed by "?", show parameter prompts
	if fullCmd == "move" && (len(parts) == 1 || (len(parts) == 2 && parts[1] == "?")) {
		return []string{
			fmt.Sprintf("%s absolute", fullCmd),
			fmt.Sprintf("%s relative", fullCmd),
			fmt.Sprintf("%s computed", fullCmd),
			fmt.Sprintf("%s <vpos> <hpos>", fullCmd),
		}
	}
	// Completion for 'move computed' to prompt shipnames in current galaxy
	if fullCmd == "move" && len(parts) == 2 && strings.ToLower(parts[1]) == "computed" {
		// Try to get the current connection's galaxy
		var galaxy uint16
		foundGalaxy := false
		if section == "gowars" && i.connections != nil {
			i.connections.Range(func(_, value interface{}) bool {
				info := value.(ConnectionInfo)
				if info.Section == "gowars" && info.Shipname != "" {
					galaxy = info.Galaxy
					foundGalaxy = true
					return false
				}
				return true
			})
		}

		var completions []string
		// Determine user's side
		userSide := ""
		if section == "gowars" {
			i.connections.Range(func(_, value interface{}) bool {
				connInfo := value.(ConnectionInfo)
				if connInfo.Section == "gowars" && connInfo.Shipname != "" {
					for _, obj := range i.objects {
						if obj.Type == "Ship" && obj.Name == connInfo.Shipname && obj.Galaxy == connInfo.Galaxy {
							userSide = obj.Side
							break
						}
					}
				}
				return userSide == ""
			})
		}
		var ships []*Object
		if foundGalaxy {
			ships = i.getObjectsByType(galaxy, "Ship")
		} else {
			// fallback: all ships in all galaxies
			for g := range i.objectsByType {
				ships = append(ships, i.getObjectsByType(g, "Ship")...)
			}
		}
		for _, obj := range ships {
			if (userSide == "federation" && obj.SeenByFed) || (userSide == "empire" && obj.SeenByEmp) {
				completions = append(completions, fmt.Sprintf("move computed %s", obj.Name))
			}
		}
		return completions
	}
	// Completion for 'move computed <prefix>' to prompt matching shipnames in current galaxy
	if fullCmd == "move" && len(parts) == 3 && strings.ToLower(parts[1]) == "computed" {
		prefix := strings.ToLower(parts[2])
		var galaxy uint16
		foundGalaxy := false
		if section == "gowars" && i.connections != nil {
			i.connections.Range(func(_, value interface{}) bool {
				info := value.(ConnectionInfo)
				if info.Section == "gowars" && info.Shipname != "" {
					galaxy = info.Galaxy
					foundGalaxy = true
					return false
				}
				return true
			})
		}

		var completions []string
		// Determine user's side
		userSide := ""
		if section == "gowars" {
			i.connections.Range(func(_, value interface{}) bool {
				connInfo := value.(ConnectionInfo)
				if connInfo.Section == "gowars" && connInfo.Shipname != "" {
					for _, obj := range i.objects {
						if obj.Type == "Ship" && obj.Name == connInfo.Shipname && obj.Galaxy == connInfo.Galaxy {
							userSide = obj.Side
							break
						}
					}
				}
				return userSide == ""
			})
		}
		var ships []*Object
		if foundGalaxy {
			ships = i.getObjectsByType(galaxy, "Ship")
		} else {
			for g := range i.objectsByType {
				ships = append(ships, i.getObjectsByType(g, "Ship")...)
			}
		}
		for _, obj := range ships {
			if strings.HasPrefix(strings.ToLower(obj.Name), prefix) {
				if (userSide == "federation" && obj.SeenByFed) || (userSide == "empire" && obj.SeenByEmp) {
					completions = append(completions, fmt.Sprintf("move computed %s", obj.Name))
				}
			}
		}
		return completions
	}
	// Enhanced completion for move: user-friendly like list command, supporting abbreviations and partial input
	if fullCmd == "move" || cmd == "mo" {
		moveParams := []string{"absolute", "relative", "computed"}
		// If entering a parameter, suggest completions for it (abbreviation support)
		if len(parts) == 2 {
			abbr := strings.ToLower(parts[1])
			matches := []string{}
			for _, param := range moveParams {
				if strings.HasPrefix(param, abbr) {
					matches = append(matches, param)
				}
			}
			if len(matches) == 1 {
				if matches[0] == "computed" {
					return []string{fmt.Sprintf("%s computed", fullCmd)}
				}
				return []string{fmt.Sprintf("%s %s <vpos> <hpos>", fullCmd, matches[0])}
			} else if len(matches) > 1 {
				return matches
			} else {
				return moveParams
			}
		}
		// If only command and a space, prompt all valid parameters (like list)
		if len(parts) == 1 && strings.HasSuffix(input, " ") {
			var completions []string
			for _, o := range moveParams {
				completions = append(completions, fmt.Sprintf("%s %s", fullCmd, o))
			}
			return completions
		}
	}

	if fullCmd == "impulse" && (len(parts) == 1 || (len(parts) == 2 && parts[1] == "?")) {
		return []string{
			fmt.Sprintf("%s absolute", fullCmd),
			fmt.Sprintf("%s relative", fullCmd),
			fmt.Sprintf("%s computed", fullCmd),
			fmt.Sprintf("%s <vpos> <hpos>", fullCmd),
		}
	}
	// Completion for 'impulse computed' to prompt shipnames in current galaxy
	if fullCmd == "impulse" && len(parts) == 2 && strings.ToLower(parts[1]) == "computed" {
		// Try to get the current connection's galaxy
		var galaxy uint16
		foundGalaxy := false
		if section == "gowars" && i.connections != nil {
			i.connections.Range(func(_, value interface{}) bool {
				info := value.(ConnectionInfo)
				if info.Section == "gowars" && info.Shipname != "" {
					galaxy = info.Galaxy
					foundGalaxy = true
					return false
				}
				return true
			})
		}

		var completions []string
		// Determine user's side
		userSide := ""
		if section == "gowars" {
			i.connections.Range(func(_, value interface{}) bool {
				connInfo := value.(ConnectionInfo)
				if connInfo.Section == "gowars" && connInfo.Shipname != "" {
					for _, obj := range i.objects {
						if obj.Type == "Ship" && obj.Name == connInfo.Shipname && obj.Galaxy == connInfo.Galaxy {
							userSide = obj.Side
							break
						}
					}
				}
				return userSide == ""
			})
		}
		var ships []*Object
		if foundGalaxy {
			ships = i.getObjectsByType(galaxy, "Ship")
		} else {
			for g := range i.objectsByType {
				ships = append(ships, i.getObjectsByType(g, "Ship")...)
			}
		}
		for _, obj := range ships {
			if (userSide == "federation" && obj.SeenByFed) || (userSide == "empire" && obj.SeenByEmp) {
				completions = append(completions, fmt.Sprintf("move computed %s", obj.Name))
			}
		}
		return completions
	}
	// Completion for 'impulse computed <prefix>' to prompt matching shipnames in current galaxy
	if fullCmd == "impulse" && len(parts) == 3 && strings.ToLower(parts[1]) == "computed" {
		prefix := strings.ToLower(parts[2])
		var galaxy uint16
		foundGalaxy := false
		if section == "gowars" && i.connections != nil {
			i.connections.Range(func(_, value interface{}) bool {
				info := value.(ConnectionInfo)
				if info.Section == "gowars" && info.Shipname != "" {
					galaxy = info.Galaxy
					foundGalaxy = true
					return false
				}
				return true
			})
		}

		var completions []string
		// Determine user's side
		userSide := ""
		if section == "gowars" {
			i.connections.Range(func(_, value interface{}) bool {
				connInfo := value.(ConnectionInfo)
				if connInfo.Section == "gowars" && connInfo.Shipname != "" {
					for _, obj := range i.objects {
						if obj.Type == "Ship" && obj.Name == connInfo.Shipname && obj.Galaxy == connInfo.Galaxy {
							userSide = obj.Side
							break
						}
					}
				}
				return userSide == ""
			})
		}
		var ships []*Object
		if foundGalaxy {
			ships = i.getObjectsByType(galaxy, "Ship")
		} else {
			for g := range i.objectsByType {
				ships = append(ships, i.getObjectsByType(g, "Ship")...)
			}
		}
		for _, obj := range ships {
			if strings.HasPrefix(strings.ToLower(obj.Name), prefix) {
				if (userSide == "federation" && obj.SeenByFed) || (userSide == "empire" && obj.SeenByEmp) {
					completions = append(completions, fmt.Sprintf("move computed %s", obj.Name))
				}
			}
		}
		return completions
	}
	// Enhanced completion for move: user-friendly like list command, supporting abbreviations and partial input
	if fullCmd == "impulse" || cmd == "im" {
		moveParams := []string{"absolute", "relative", "computed"}
		// If entering a parameter, suggest completions for it (abbreviation support)
		if len(parts) == 2 {
			abbr := strings.ToLower(parts[1])
			matches := []string{}
			for _, param := range moveParams {
				if strings.HasPrefix(param, abbr) {
					matches = append(matches, param)
				}
			}
			if len(matches) == 1 {
				if matches[0] == "computed" {
					return []string{fmt.Sprintf("%s computed", fullCmd)}
				}
				return []string{fmt.Sprintf("%s %s <vpos> <hpos>", fullCmd, matches[0])}
			} else if len(matches) > 1 {
				return matches
			} else {
				return moveParams
			}
		}
		// If only command and a space, prompt all valid parameters (like list)
		if len(parts) == 1 && strings.HasSuffix(input, " ") {
			var completions []string
			for _, o := range moveParams {
				completions = append(completions, fmt.Sprintf("%s %s", fullCmd, o))
			}
			return completions
		}
	}
	// Completion for 'phasers computed <prefix>' to prompt matching shipnames in current galaxy
	if (fullCmd == "phasers" || cmd == "phas") && len(parts) == 3 && strings.ToLower(parts[1]) == "computed" {
		prefix := strings.ToLower(parts[2])
		if prefix == "?" {
			prefix = ""
		}
		// Get the user's galaxy from connection info
		var galaxy uint16 = 0
		if conn != nil {
			if info, ok := i.connections.Load(conn); ok {
				connInfo := info.(ConnectionInfo)
				if connInfo.Section == "gowars" && connInfo.Shipname != "" {
					galaxy = connInfo.Galaxy
				}
			}
		}

		var completions []string
		for _, obj := range i.getObjectsByType(galaxy, "Ship") {
			if strings.HasPrefix(strings.ToLower(obj.Name), prefix) {
				cmdName := "phasers"
				if cmd == "phas" {
					cmdName = "phas"
				}
				completions = append(completions, fmt.Sprintf("%s computed %s", cmdName, obj.Name))
			}
		}
		if len(completions) == 1 {
			return completions // auto-complete to the full ship name
		}
		return completions
	}
	// Completion for 'phasers computed' to prompt shipnames in current galaxy
	if (fullCmd == "phasers" || cmd == "phas") && len(parts) == 2 && strings.ToLower(parts[1]) == "computed" {
		// Get the user's galaxy from connection info
		var galaxy uint16 = 0
		if conn != nil {
			if info, ok := i.connections.Load(conn); ok {
				connInfo := info.(ConnectionInfo)
				if connInfo.Section == "gowars" && connInfo.Shipname != "" {
					galaxy = connInfo.Galaxy
				}
			}
		}

		var completions []string
		for _, obj := range i.getObjectsByType(galaxy, "Ship") {
			cmdName := "phasers"
			if cmd == "phas" {
				cmdName = "phas"
			}
			completions = append(completions, fmt.Sprintf("%s computed %s", cmdName, obj.Name))
		}
		return completions
	}
	// Completion for 'phasers computed <prefix>' to prompt matching shipnames in current galaxy
	if (fullCmd == "phasers" || cmd == "phas") && len(parts) == 3 && strings.ToLower(parts[1]) == "computed" {
		prefix := strings.ToLower(parts[2])
		// Get the user's galaxy from connection info
		var galaxy uint16 = 0
		if conn != nil {
			if info, ok := i.connections.Load(conn); ok {
				connInfo := info.(ConnectionInfo)
				if connInfo.Section == "gowars" && connInfo.Shipname != "" {
					galaxy = connInfo.Galaxy
				}
			}
		}

		var completions []string
		for _, obj := range i.getObjectsByType(galaxy, "Ship") {
			if strings.HasPrefix(strings.ToLower(obj.Name), prefix) {
				cmdName := "phasers"
				if cmd == "phas" {
					cmdName = "phas"
				}
				completions = append(completions, fmt.Sprintf("%s computed %s", cmdName, obj.Name))
			}
		}
		if len(completions) == 1 {
			return completions // auto-complete to the full ship name
		}
		return completions
	}
	// Enhanced completion for phasers: user-friendly like other commands, supporting abbreviations and partial input
	// But only when NOT "computed" mode (handled separately above)
	if (fullCmd == "phasers" || cmd == "ph" || cmd == "phas") && !(len(parts) == 2 && strings.ToLower(parts[1]) == "computed") {
		phaserParams := []string{"absolute", "relative", "computed"}
		// If entering a parameter, suggest completions for it (abbreviation support)
		if len(parts) == 2 {
			abbr := strings.ToLower(parts[1])
			matches := []string{}
			for _, param := range phaserParams {
				if strings.HasPrefix(param, abbr) {
					matches = append(matches, param)
				}
			}
			if len(matches) == 1 {
				return []string{fmt.Sprintf("%s %s", fullCmd, matches[0])}
			} else if len(matches) > 1 {
				return matches
			} else {
				return phaserParams
			}
		}
		// If only command and a space, prompt all valid parameters
		if len(parts) == 1 && strings.HasSuffix(input, " ") {
			var completions []string
			for _, o := range phaserParams {
				completions = append(completions, fmt.Sprintf("%s %s", fullCmd, o))
			}
			return completions
		}
	}
	// Enhanced completion for torpedoes: user-friendly like other commands, supporting abbreviations and partial input
	if fullCmd == "torpedoes" || cmd == "to" {
		// Parameter completion for "torpedoes computed <shipname>" (with abbreviation support)
		if len(parts) >= 2 {
			validModes := map[string]bool{"computed": true}
			if mode, ok := i.resolveParameter(strings.ToLower(parts[1]), validModes); ok && mode == "computed" {
				prefix := ""
				if len(parts) >= 3 {
					prefix = strings.ToLower(parts[2])
				}
				var completions []string
				// Get the user's current galaxy
				var userGalaxy uint16
				if conn != nil {
					if info, ok := i.connections.Load(conn); ok {
						userGalaxy = info.(ConnectionInfo).Galaxy
					}
				}

				// Suggest shipnames in the user's galaxy using objectsByType

				for _, obj := range i.getObjectsByType(userGalaxy, "Ship") {
					if strings.HasPrefix(strings.ToLower(obj.Name), prefix) {
						completions = append(completions, fmt.Sprintf("%s %s %s", fullCmd, "computed", obj.Name))
					}
				}

				sort.Strings(completions)
				if len(completions) > 0 {
					return completions
				}
			}
		}
		torpedoParams := []string{"absolute", "relative", "computed"}
		// If entering a parameter, suggest completions for it (abbreviation support)
		if len(parts) == 2 {
			abbr := strings.ToLower(parts[1])
			matches := []string{}
			for _, param := range torpedoParams {
				if strings.HasPrefix(param, abbr) {
					matches = append(matches, param)
				}
			}
			if len(matches) == 1 {
				return []string{fmt.Sprintf("%s %s", fullCmd, matches[0])}
			} else if len(matches) > 1 {
				return matches
			} else {
				return torpedoParams
			}
		}
		// If only command and a space, prompt all valid parameters
		if len(parts) == 1 && strings.HasSuffix(input, " ") {
			var completions []string
			for _, o := range torpedoParams {
				completions = append(completions, fmt.Sprintf("%s %s", fullCmd, o))
			}
			return completions
		}
	}

	// Parameter completion for "torpedoes computed <shipname>" (with abbreviation support)
	if (fullCmd == "torpedoes" || cmd == "to") && len(parts) >= 2 {
		validModes := map[string]bool{"computed": true}
		if mode, ok := i.resolveParameter(strings.ToLower(parts[1]), validModes); ok && mode == "computed" {
			prefix := ""
			if len(parts) >= 3 {
				prefix = strings.ToLower(parts[2])
			}
			var completions []string

			// Get the user's current galaxy
			var userGalaxy uint16
			if conn != nil {
				if info, ok := i.connections.Load(conn); ok {
					userGalaxy = info.(ConnectionInfo).Galaxy
				}
			}

			// Suggest shipnames in the user's galaxy
			i.connections.Range(func(_, value interface{}) bool {
				info := value.(ConnectionInfo)
				if info.Shipname != "" && info.Galaxy == userGalaxy && strings.HasPrefix(strings.ToLower(info.Shipname), prefix) {
					completions = append(completions, fmt.Sprintf("%s %s %s", fullCmd, "computed", info.Shipname))
				}
				return true
			})
			sort.Strings(completions)
			if len(completions) > 0 {
				return completions
			}
		}
	}

	switch fullCmd {
	case "dock":
		dockParams := []string{"status", "warp", "impulse", "torpedos", "phasers", "shields", "computer", "lifesupport", "radio", "tractor"}
		// If only command and a space, or "dock ?", prompt for parameters (like list)
		if (len(parts) == 1 && strings.HasSuffix(input, " ")) || (len(parts) == 2 && (parts[1] == "?" || strings.TrimSpace(parts[1]) == "?")) {
			var completions []string
			for _, param := range dockParams {
				completions = append(completions, fmt.Sprintf("%s %s", fullCmd, param))
			}
			return completions
		}
		// Multi-parameter completion logic (as before)
		var completedParams []string
		var ambiguousParams [][]string
		for i := 1; i < len(parts); i++ {
			abbr := strings.ToLower(parts[i])
			matches := []string{}
			for _, param := range dockParams {
				if strings.HasPrefix(strings.ToLower(param), abbr) {
					matches = append(matches, param)
				}
			}
			if len(matches) == 1 {
				completedParams = append(completedParams, matches[0])
			} else if len(matches) > 1 {
				ambiguousParams = append(ambiguousParams, matches)
				completedParams = append(completedParams, parts[i]) // keep original for ambiguous
			} else {
				ambiguousParams = append(ambiguousParams, dockParams)
				completedParams = append(completedParams, parts[i]) // keep original for no match
			}
		}
		// If all parameters are unambiguous, return the completed command line
		if len(ambiguousParams) == 0 {
			return []string{fmt.Sprintf("%s %s", fullCmd, strings.Join(completedParams, " "))}
		} else {
			// If any ambiguous or unmatched, show all possible completions for those parameters
			var completions []string
			for _, params := range ambiguousParams {
				completions = append(completions, params...)
			}
			return completions
		}
	case "help", "?":
		if len(parts) == 1 || (len(parts) == 2 && !strings.HasSuffix(input, " ")) {
			var completions []string
			prefix := ""
			if len(parts) == 2 {
				prefix = strings.ToLower(parts[1])
			}
			for cmdName := range commands {
				if strings.HasPrefix(cmdName, prefix) {
					completions = append(completions, fmt.Sprintf("%s %s", fullCmd, cmdName))
				}
			}
			sort.Strings(completions)
			return completions
		}
	case "tell":
		if len(parts) == 1 || (len(parts) == 2 && !strings.HasSuffix(input, " ")) {
			var completions []string
			prefix := ""
			if len(parts) == 2 {
				prefix = strings.ToLower(parts[1])
			}

			info, ok := i.connections.Load(conn)
			if ok {
				connInfo := info.(ConnectionInfo)

				if connInfo.Section == "gowars" {
					// In gowars mode: show optional parameters and shipnames, but NOT connections
					params := []string{"all", "federation", "human", "empire", "klingon", "enemy", "friendly"}
					for _, param := range params {
						if strings.HasPrefix(param, prefix) {
							abbr := i.getAbbreviation(param, params)
							completions = append(completions, fmt.Sprintf("%s %s", fullCmd, abbr))
						}
					}

					// Suggest shipnames from user's current galaxy using objectsByType
					userGalaxy := connInfo.Galaxy

					for _, obj := range i.getObjectsByType(userGalaxy, "Ship") {
						if strings.HasPrefix(strings.ToLower(obj.Name), prefix) {
							completions = append(completions, fmt.Sprintf("%s %s", fullCmd, obj.Name))
						}
					}

				} else {
					// In pregame mode: show connections only (usernames and ports)
					i.connections.Range(func(_, value interface{}) bool {
						info := value.(ConnectionInfo)
						if info.Name != "" && strings.HasPrefix(strings.ToLower(info.Name), prefix) {
							completions = append(completions, fmt.Sprintf("%s %s", fullCmd, info.Name))
						}
						if info.Port != "" && strings.HasPrefix(info.Port, prefix) {
							completions = append(completions, fmt.Sprintf("%s %s", fullCmd, info.Port))
						}
						return true
					})
				}
			}
			sort.Strings(completions)
			return completions
		}
	case "energy":
		// Completion for: energy <shipname>
		if len(parts) == 1 || (len(parts) == 2 && !strings.HasSuffix(input, " ")) {
			var completions []string
			prefix := ""
			if len(parts) == 2 {
				prefix = strings.ToLower(parts[1])
			}
			// Suggest shipnames in user's galaxy using objectsByType
			var userGalaxy uint16 = 0
			if conn != nil {
				if info, ok := i.connections.Load(conn); ok {
					userGalaxy = info.(ConnectionInfo).Galaxy
				}
			}
			for _, obj := range i.getObjectsByType(userGalaxy, "Ship") {
				if strings.HasPrefix(strings.ToLower(obj.Name), prefix) {
					completions = append(completions, fmt.Sprintf("%s %s", fullCmd, obj.Name))
				}
			}

			sort.Strings(completions)
			return completions
		}

	case "bases":
		if section == "gowars" {
			// Handle parameter completion for bases command
			if len(parts) == 1 || (len(parts) == 2 && !strings.HasSuffix(input, " ")) {
				var completions []string
				prefix := ""
				if len(parts) == 2 {
					prefix = strings.ToLower(parts[1])
				}

				// Check if prefix could be a number (for coordinates)
				_, err := strconv.Atoi(prefix)
				if err == nil {
					completions = append(completions, fmt.Sprintf("%s %s <hpos>", fullCmd, prefix))
					return completions
				}

				keywords := []string{"enemy", "sum", "all", "closest"}
				for _, kw := range keywords {
					if strings.HasPrefix(kw, prefix) {
						abbr := i.getAbbreviation(kw, keywords)
						completions = append(completions, fmt.Sprintf("%s %s", fullCmd, abbr))
					}
				}
				sort.Strings(completions)
				return completions
			}

			// If first parameter is a number, expect a second number
			if len(parts) == 2 && strings.HasSuffix(input, " ") {
				_, err := strconv.Atoi(parts[1])
				if err == nil {
					return []string{fmt.Sprintf("%s %s <hpos>", fullCmd, parts[1])}
				}
			}

			// After the first parameter (or more), allow additional parameters
			if (len(parts) >= 2 && strings.HasSuffix(input, " ")) || (len(parts) >= 3) {
				var completions []string
				prefix := ""
				if !strings.HasSuffix(input, " ") {
					prefix = strings.ToLower(parts[len(parts)-1])
				}

				// Check if we already have coordinates in the first two parameters
				vposParam, err1 := strconv.Atoi(parts[1])
				if err1 == nil && len(parts) >= 3 {
					hposParam, err2 := strconv.Atoi(parts[2])
					if err2 == nil {
						// If we already have coordinates, suggest other parameters
						keywords := []string{"enemy", "sum", "all", "closest"}

						// Check which keywords are already used in the command
						usedKeywords := make(map[string]bool)
						for i := 3; i < len(parts); i++ {
							for _, kw := range keywords {
								if strings.HasPrefix(kw, strings.ToLower(parts[i])) {
									usedKeywords[kw] = true
								}
							}
						}

						for _, kw := range keywords {
							if !usedKeywords[kw] && strings.HasPrefix(kw, prefix) {
								abbr := i.getAbbreviation(kw, keywords)
								coordPart := fmt.Sprintf("%s %d %d", fullCmd, vposParam, hposParam)

								// Add any parameters that have already been used
								for i := 3; i < len(parts)-1; i++ {
									coordPart += " " + parts[i]
								}

								completions = append(completions, fmt.Sprintf("%s %s", coordPart, abbr))
							}
						}
						sort.Strings(completions)
						return completions
					}
				}

				// Otherwise, suggest remaining valid parameters
				alreadyUsed := make(map[string]bool)
				for i := 1; i < len(parts); i++ {
					param := strings.ToLower(parts[i])
					_, err := strconv.Atoi(param)
					if err != nil { // Not a number, so it's a parameter
						alreadyUsed[param] = true
					}
				}

				keywords := []string{"enemy", "sum", "all", "closest"}
				for _, kw := range keywords {
					if !alreadyUsed[kw] && strings.HasPrefix(kw, prefix) {
						abbr := i.getAbbreviation(kw, keywords)

						// Correctly preserve all previous parts of the command
						var basePart string
						if strings.HasSuffix(input, " ") {
							basePart = input[:len(input)-1]
						} else {
							// Remove the incomplete parameter being typed
							basePart = strings.Join(parts[:len(parts)-1], " ")
						}

						completions = append(completions, fmt.Sprintf("%s %s", basePart, abbr))
					}
				}
				sort.Strings(completions)
				return completions
			}
		}
	case "list":
		if section == "gowars" {
			if len(parts) == 1 || (len(parts) == 2 && !strings.HasSuffix(input, " ")) {
				var completions []string
				prefix := ""
				if len(parts) == 2 {
					prefix = strings.ToLower(parts[1])
				}
				keywords := []string{"neutral", "friendly", "enemy", "closest", "ships", "bases", "planets", "summary", "ports", "captured"}
				for _, kw := range keywords {
					if strings.HasPrefix(kw, prefix) {
						abbr := i.getAbbreviation(kw, keywords)
						completions = append(completions, fmt.Sprintf("%s %s", fullCmd, abbr))
					}
				}
				sort.Strings(completions)
				// Add <radius> as a possible completion at the top level
				completions = append(completions, fmt.Sprintf("%s <radius>", fullCmd))
				return completions
			}

			if len(parts) == 2 && parts[1] == "closest" && strings.HasSuffix(input, " ") ||
				(len(parts) == 3 && !strings.HasSuffix(input, " ")) {
				var completions []string
				prefix := ""
				if len(parts) == 3 {
					prefix = strings.ToLower(parts[2])
				}
				types := []string{"base", "enemy", "friendly", "neutral", "planet", "star", "ship", "blackhole"}
				for _, t := range types {
					if strings.HasPrefix(t, prefix) {
						abbr := i.getAbbreviation(t, types)
						completions = append(completions, fmt.Sprintf("%s closest %s", fullCmd, abbr))
					}
				}
				sort.Strings(completions)
				return completions
			}
		}
	case "scan":
	case "planets":
		// Parameter completion for planets command, including partials
		if len(parts) == 1 || (len(parts) == 2 && !strings.HasSuffix(input, " ")) {
			var completions []string
			prefix := ""
			if len(parts) == 2 {
				prefix = strings.ToLower(parts[1])
			}
			options := []string{"sum", "all"}

			// Check if the prefix matches "all" - if so, we should show sub-parameter options
			if prefix == "all" {
				// User typed exactly "all" - show sub-parameter options
				subOptions := []string{"neutral", "captured"}
				for _, opt := range subOptions {
					completions = append(completions, fmt.Sprintf("%s all %s", fullCmd, opt))
				}
				completions = append(completions, fmt.Sprintf("%s all <range>", fullCmd))
				sort.Strings(completions)
				return completions
			}

			// Regular parameter completion
			for _, opt := range options {
				if strings.HasPrefix(opt, prefix) {
					completions = append(completions, fmt.Sprintf("%s %s", fullCmd, opt))
				}
			}
			if len(completions) == 0 && prefix != "" {
				// If no match, show all options for ambiguous/invalid partial
				for _, opt := range options {
					completions = append(completions, fmt.Sprintf("%s %s", fullCmd, opt))
				}
			}
			if prefix == "" {
				completions = append(completions, fmt.Sprintf("%s <parameter>", fullCmd))
			}
			sort.Strings(completions)
			return completions
		}

		// Handle "planets all" sub-parameter completion when there's a space after "all"
		if len(parts) == 2 && strings.ToLower(parts[1]) == "all" && strings.HasSuffix(input, " ") ||
			(len(parts) == 3 && strings.ToLower(parts[1]) == "all" && !strings.HasSuffix(input, " ")) {
			var completions []string
			prefix := ""
			if len(parts) == 3 {
				prefix = strings.ToLower(parts[2])
			}
			subOptions := []string{"neutral", "captured"}
			for _, opt := range subOptions {
				if strings.HasPrefix(opt, prefix) {
					completions = append(completions, fmt.Sprintf("%s all %s", fullCmd, opt))
				}
			}
			if prefix == "" {
				completions = append(completions, fmt.Sprintf("%s all <range>", fullCmd))
			}
			sort.Strings(completions)
			return completions
		}
		if len(parts) == 2 && strings.HasSuffix(input, " ") || (len(parts) == 3 && !strings.HasSuffix(input, " ")) {
			var completions []string
			prefix := ""
			if len(parts) == 3 {
				prefix = strings.ToLower(parts[2])
			}
			options := []string{"warn"}
			for _, opt := range options {
				if strings.HasPrefix(opt, prefix) {
					completions = append(completions, fmt.Sprintf("%s %s %s", fullCmd, parts[1], opt))
				}
			}
			if prefix == "" {
				completions = append(completions, fmt.Sprintf("%s %s <number>", fullCmd, parts[1]))
			}
			sort.Strings(completions)
			return completions
		}
		if len(parts) == 3 && strings.HasSuffix(input, " ") || (len(parts) == 4 && !strings.HasSuffix(input, " ")) {
			var completions []string
			prefix := ""
			if len(parts) == 4 {
				prefix = strings.ToLower(parts[3])
			}
			options := []string{"warn"}
			for _, opt := range options {
				if strings.HasPrefix(opt, prefix) {
					completions = append(completions, fmt.Sprintf("%s %s %s %s", fullCmd, parts[1], parts[2], opt))
				}
			}
			if prefix == "" {
				completions = append(completions, fmt.Sprintf("%s %s %s <number>", fullCmd, parts[1], parts[2]))
			}
			sort.Strings(completions)
			return completions
		}
		if len(parts) == 4 && strings.HasSuffix(input, " ") || (len(parts) == 5 && !strings.HasSuffix(input, " ")) {
			var completions []string
			prefix := ""
			if len(parts) == 5 {
				prefix = strings.ToLower(parts[4])
			}
			options := []string{"warn"}
			for _, opt := range options {
				if strings.HasPrefix(opt, prefix) {
					completions = append(completions, fmt.Sprintf("%s %s %s %s %s", fullCmd, parts[1], parts[2], parts[3], opt))
				}
			}
			sort.Strings(completions)
			return completions
		}
	case "srscan":
		if (len(parts) == 1 && strings.HasSuffix(input, " ")) || (len(parts) == 2 && !strings.HasSuffix(input, " ")) {
			var completions []string
			prefix := ""
			if len(parts) == 2 {
				prefix = strings.ToLower(parts[1])
			}
			options := []string{"up", "down", "right", "left", "corner", "warn"}
			for _, opt := range options {
				if strings.HasPrefix(opt, prefix) {
					completions = append(completions, fmt.Sprintf("%s %s", fullCmd, opt))
				}
			}
			completions = append(completions, fmt.Sprintf("%s <number>", fullCmd))
			sort.Strings(completions)
			return completions
		} else if (len(parts) == 2 && strings.HasSuffix(input, " ")) || (len(parts) == 3 && !strings.HasSuffix(input, " ")) {
			var completions []string
			prefix := ""
			if len(parts) == 3 {
				prefix = strings.ToLower(parts[2])
			}
			if strings.HasPrefix("warn", prefix) {
				completions = append(completions, fmt.Sprintf("%s %s warn", fullCmd, parts[1]))
			}
			completions = append(completions, fmt.Sprintf("%s %s <number>", fullCmd, parts[1]))
			return completions
		} else if (len(parts) == 3 && strings.HasSuffix(input, " ")) || (len(parts) == 4 && !strings.HasSuffix(input, " ")) {
			var completions []string
			prefix := ""
			if len(parts) == 4 {
				prefix = strings.ToLower(parts[3])
			}
			if strings.HasPrefix("warn", prefix) {
				completions = append(completions, fmt.Sprintf("%s %s %s warn", fullCmd, parts[1], parts[2]))
			}
			completions = append(completions, fmt.Sprintf("%s %s %s <number>", fullCmd, parts[1], parts[2]))
			return completions
		} else if (len(parts) == 4 && strings.HasSuffix(input, " ")) || (len(parts) == 5 && !strings.HasSuffix(input, " ")) {
			var completions []string
			prefix := ""
			if len(parts) == 5 {
				prefix = strings.ToLower(parts[4])
			}
			if strings.HasPrefix("warn", prefix) {
				completions = append(completions, fmt.Sprintf("%s %s %s %s warn", fullCmd, parts[1], parts[2], parts[3]))
			}
			return completions
		}
	case "set":
		// Enable parameter prompting/completion for both pregame and gowars
		if section == "gowars" || section == "pregame" {
			if len(parts) == 1 || (len(parts) == 2 && !strings.HasSuffix(input, " ")) {
				var completions []string
				prefix := ""
				if len(parts) == 2 {
					prefix = strings.ToLower(parts[1])
				}
				parameters := []string{"prompt", "output", "OCdef", "scan", "icdef", "name", "baud"}
				for _, param := range parameters {
					if strings.HasPrefix(strings.ToLower(param), prefix) {
						abbr := i.getAbbreviation(param, parameters)
						completions = append(completions, fmt.Sprintf("%s %s", fullCmd, abbr))
					}
				}
				sort.Strings(completions)
				return completions
			}
			// Handle sub-parameter values
			if len(parts) >= 2 {
				param := strings.ToLower(parts[1])
				switch param {
				case "output":
					if len(parts) == 2 && strings.HasSuffix(input, " ") ||
						(len(parts) == 3 && !strings.HasSuffix(input, " ")) {
						var completions []string
						prefix := ""
						if len(parts) == 3 {
							prefix = strings.ToLower(parts[2])
						}
						values := []string{"long", "medium", "short"}
						for _, v := range values {
							if strings.HasPrefix(v, prefix) {
								completions = append(completions, fmt.Sprintf("%s output %s", fullCmd, v))
							}
						}
						sort.Strings(completions)
						return completions
					}
				case "ocdef":
					if len(parts) == 2 && strings.HasSuffix(input, " ") ||
						(len(parts) == 3 && !strings.HasSuffix(input, " ")) {
						var completions []string
						prefix := ""
						if len(parts) == 3 {
							prefix = strings.ToLower(parts[2])
						}
						values := []string{"relative", "absolute", "both"}
						for _, v := range values {
							if strings.HasPrefix(v, prefix) {
								completions = append(completions, fmt.Sprintf("%s ocdef %s", fullCmd, v))
							}
						}
						sort.Strings(completions)
						return completions
					}
				case "scan":
					if len(parts) == 2 && strings.HasSuffix(input, " ") ||
						(len(parts) == 3 && !strings.HasSuffix(input, " ")) {
						var completions []string
						prefix := ""
						if len(parts) == 3 {
							prefix = strings.ToLower(parts[2])
						}
						values := []string{"long", "short"}
						for _, v := range values {
							if strings.HasPrefix(v, prefix) {
								completions = append(completions, fmt.Sprintf("%s scan %s", fullCmd, v))
							}
						}
						sort.Strings(completions)
						return completions
					}
				case "prompt":
					if (len(parts) == 2 && strings.HasSuffix(input, " ")) ||
						(len(parts) == 3 && (!strings.HasSuffix(input, " ") || parts[2] == "?")) {
						var completions []string
						prefix := ""
						if len(parts) == 3 {
							prefix = strings.ToLower(parts[2])
						}
						values := []string{"normal", "informative"}
						for _, v := range values {
							if strings.HasPrefix(v, prefix) {
								completions = append(completions, fmt.Sprintf("%s prompt %s", fullCmd, v))
							}
						}
						sort.Strings(completions)
						return completions
					}
				case "icdef":
					if len(parts) == 2 && strings.HasSuffix(input, " ") ||
						(len(parts) == 3 && !strings.HasSuffix(input, " ")) {
						var completions []string
						prefix := ""
						if len(parts) == 3 {
							prefix = strings.ToLower(parts[2])
						}
						values := []string{"relative", "absolute"}
						for _, v := range values {
							if strings.HasPrefix(v, prefix) {
								completions = append(completions, fmt.Sprintf("%s icdef %s", fullCmd, v))
							}
						}
						sort.Strings(completions)
						return completions
					}
				case "name":
					if len(parts) == 2 && strings.HasSuffix(input, " ") ||
						(len(parts) == 3 && !strings.HasSuffix(input, " ")) {
						var completions []string
						prefix := ""
						if len(parts) == 3 {
							prefix = parts[2]
						}
						// For name, just echo the prefix as a suggestion
						if prefix != "" {
							completions = append(completions, fmt.Sprintf("%s name %s", fullCmd, prefix))
						}
						return completions
					}
				case "baud":
					if len(parts) == 2 && strings.HasSuffix(input, " ") ||
						(len(parts) == 3 && !strings.HasSuffix(input, " ")) {
						var completions []string
						prefix := ""
						if len(parts) == 3 {
							prefix = strings.ToLower(parts[2])
						}
						values := []string{"0", "300", "1200", "2400", "9600"}
						for _, v := range values {
							if strings.HasPrefix(v, prefix) {
								completions = append(completions, fmt.Sprintf("%s baud %s", fullCmd, v))
							}
						}
						sort.Strings(completions)
						return completions
					}
				}
			}
		}
	case "activate":
		if len(parts) == 2 && strings.HasSuffix(input, " ") || (len(parts) == 3 && !strings.HasSuffix(input, " ")) {
			// First parameter completion: Side options
			var completions []string
			prefix := ""
			if len(parts) == 3 {
				prefix = strings.ToLower(parts[2])
			}
			sides := []string{"federation", "empire", "fed", "emp"}
			for _, side := range sides {
				if strings.HasPrefix(side, prefix) {
					completions = append(completions, fmt.Sprintf("%s %s %s", fullCmd, parts[1], side))
				}
			}
			// Also include galaxy numbers as first parameter (backward compatibility)
			galaxySet := make(map[uint16]struct{})
			for _, obj := range i.objects {
				galaxySet[obj.Galaxy] = struct{}{}
			}
			for galaxy := range galaxySet {
				galaxyStr := fmt.Sprintf("%d", galaxy)
				if strings.HasPrefix(galaxyStr, prefix) {
					completions = append(completions, fmt.Sprintf("%s %s %s", fullCmd, parts[1], galaxyStr))
				}
			}
			sort.Strings(completions)
			return completions
		}
		if len(parts) == 3 && strings.HasSuffix(input, " ") || (len(parts) == 4 && !strings.HasSuffix(input, " ")) {
			// Second parameter completion: Galaxy numbers (when first param is side)
			var completions []string
			prefix := ""
			if len(parts) == 4 {
				prefix = parts[3]
			}
			firstArg := strings.ToLower(parts[2])
			// Only show galaxy completions if first argument looks like a side
			if firstArg == "f" || strings.HasPrefix("federation", firstArg) ||
				firstArg == "e" || strings.HasPrefix("empire", firstArg) {
				galaxySet := make(map[uint16]struct{})
				for _, obj := range i.objects {
					galaxySet[obj.Galaxy] = struct{}{}
				}
				for galaxy := range galaxySet {
					galaxyStr := fmt.Sprintf("%d", galaxy)
					if strings.HasPrefix(galaxyStr, prefix) {
						completions = append(completions, fmt.Sprintf("%s %s %s %s", fullCmd, parts[1], parts[2], galaxyStr))
					}
				}
				sort.Strings(completions)
			}
			return completions
		}
	case "summary":
		if section == "gowars" {
			if len(parts) == 1 || (len(parts) == 2 && !strings.HasSuffix(input, " ")) {
				var completions []string
				prefix := ""
				if len(parts) == 2 {
					prefix = strings.ToLower(parts[1])
				}
				params := []string{"ships", "bases", "planets", "friendly", "enemy"}
				for _, param := range params {
					if strings.HasPrefix(param, prefix) {
						abbr := i.getAbbreviation(param, params)
						completions = append(completions, fmt.Sprintf("%s %s", fullCmd, abbr))
					}
				}
				sort.Strings(completions)
				return completions
			}
		}
	}
	return []string{}
}

// resolveCommand resolves abbreviated commands based on section
func (i *Interpreter) resolveCommand(input string, section string) (string, bool) {
	input = strings.ToLower(input)
	commands := i.pregameCommands
	if section == "gowars" {
		commands = i.gowarsCommands
	}
	var matches []string
	for cmd := range commands {
		if strings.HasPrefix(cmd, input) {
			matches = append(matches, cmd)
		}
	}
	if len(matches) == 1 {
		return matches[0], true
	}
	// If there are multiple matches, check for an exact match
	if len(matches) > 1 {
		for _, match := range matches {
			if match == input {
				return match, true
			}
		}
	}
	return "", false // No match or ambiguous
}

// getPrompt returns the appropriate prompt based on section
func (i *Interpreter) getPrompt(conn net.Conn) string {
	if info, ok := i.connections.Load(conn); ok {
		connInfo := info.(ConnectionInfo)
		if connInfo.Section == "gowars" {
			// Custom prompt logic for "normal" prompt
			if strings.ToLower(connInfo.Prompt) == "informative" || connInfo.Prompt == "" {
				prefix := ""
				// Use direct ship pointer
				if connInfo.Ship != nil {
					ship := connInfo.Ship
					// LifeSupportReserve + "L" if LifeSupportDamage > 300
					if ship.LifeSupportDamage > 300 {
						prefix += fmt.Sprintf("%dL", ship.LifeSupportReserve)
					}
					// "S" if ShieldsUpDown == false or Shields < 10%
					if !ship.ShieldsUpDown || (ship.Shields < InitialShieldValue/10) {
						prefix += "S"
					}
					// "E" if ShipEnergy < 1000
					if ship.ShipEnergy < 1000 {
						prefix += "E"
					}
				}
				return prefix + "> "
			} else {
				return "Command: "
			}
		}
	}
	return "PG> "
}

// handleConnection processes input from a single client over TCP
func (i *Interpreter) handleConnection(conn net.Conn) {
	defer conn.Close()

	addr := conn.RemoteAddr().String()
	ip, port, _ := net.SplitHostPort(addr)
	startTime := time.Now()
	baudRate := 0 // Always start at 0 in pregame
	writer := bufio.NewWriter(conn)
	info := ConnectionInfo{
		IP:             ip,
		Port:           port,
		ConnTime:       startTime,
		LastActivity:   startTime,
		Section:        "pregame",
		Shipname:       "",
		Galaxy:         0,
		OutputState:    "long",
		Prompt:         "",
		OCdef:          "both",
		Scan:           "long",
		ICdef:          "relative",
		Name:           "",
		RangeWarn:      false,
		BaudRate:       baudRate, // Set according to DecwarMode
		AdminMode:      false,
		CmdRateLimiter: NewTokenBucket(20, 5), // burst 20, refill 5/sec
	}
	i.connections.Store(conn, info)
	i.writers.Store(conn, writer)
	i.writerMutexs.Store(conn, &sync.Mutex{})

	// Create context that gets cancelled when connection is lost
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()

	defer func() {
		cancel() // Cancel context on exit
		if info, ok := i.connections.Load(conn); ok {
			connInfo := info.(ConnectionInfo)
			// Close CommandQueue if it exists to signal processor goroutine to exit
			if connInfo.CommandQueue != nil {
				close(connInfo.CommandQueue)
				connInfo.CommandQueue = nil
				i.connections.Store(conn, connInfo)
			}
			if connInfo.Shipname != "" {
				// Find the ship object and call cleanupShip to handle tractor beam cleanup
				for j := range i.objects {
					obj := i.objects[j]
					if obj.Type == "Ship" && obj.Name == connInfo.Shipname && obj.Galaxy == connInfo.Galaxy {
						i.cleanupShip(obj)
						break
					}
				}
			}
		}
		i.connections.Delete(conn)
		i.writers.Delete(conn)
		i.writerMutexs.Delete(conn)
	}()

	reader := bufio.NewReader(conn)

	neg := []byte{IAC, DO, LINEMODE, IAC, WONT, LINEMODE, IAC, WILL, ECHO}
	conn.Write(neg)

	time.Sleep(100 * time.Millisecond)

	// Consume initial telnet negotiation bytes
	for {
		conn.SetReadDeadline(time.Now().Add(500 * time.Millisecond))
		char, err := reader.ReadByte()
		if err != nil {
			if netErr, ok := err.(net.Error); ok && netErr.Timeout() {
				break
			}
			break
		}
		if char == IAC {
			cmd, err := reader.ReadByte()
			if err != nil {
				break
			}
			opt, err := reader.ReadByte()
			if err != nil {
				break
			}
			_ = cmd
			_ = opt
		}
	}

	conn.SetReadDeadline(time.Time{})

	// Send notification that a connection has occurred using nfty.sh
	/*	url := "https://ntfy.sh/Gowars" // Full URL (curl adds https:// implicitly)
		connInfoStr := fmt.Sprintf("%s:%s", info.IP, info.Port)
		message := "Connection to Gowars from: " + connInfoStr

		// Create the POST request
		resp, err := http.Post(url, "text/plain", strings.NewReader(message))
		if err != nil {
			log.Fatalf("Request failed: %v", err)
		}
		defer resp.Body.Close() */
	//

	i.writeBaudf(conn, writer, "Enter Help\r\n")
	i.writeBaudf(conn, writer, gowarVersion)
	i.writeBaudf(conn, writer, "For a list of commands type Help or ?\r\n")
	i.writeBaudf(conn, writer, "Upper case letters mark the shortest acceptable abbreviation.\r\n")
	i.writeBaudf(conn, writer, "For help on a particular command type Help command (ex: help help)\r\n")

	// Print the prompt immediately after welcome/help message
	prompt := i.getPrompt(conn)
	if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
		mutex := mutexRaw.(*sync.Mutex)
		mutex.Lock()
		fmt.Fprintf(writer, "%s", prompt)
		writer.Flush()
		mutex.Unlock()
	}

	done := make(chan struct{})
	go func() {
		ticker := time.NewTicker(1 * time.Minute)
		defer ticker.Stop()
		for {
			select {
			case <-done:
				return
			case <-ctx.Done():
				return
			case <-ticker.C:
				if info, ok := i.connections.Load(conn); ok {
					connInfo := info.(ConnectionInfo)
					if time.Since(connInfo.LastActivity) > MaxIdleTime*time.Minute {
						if writerRaw, ok := i.writers.Load(conn); ok {
							writer := writerRaw.(*bufio.Writer)
							i.writeBaudf(conn, writer, "\r\nDisconnected due to inactivity.\r\n")
						}
						conn.Close()
						cancel() // Cancel context on timeout
						return
					}
				}
			}
		}
	}()
	defer close(done)

	var currentInput strings.Builder
	var cursorPos int // Tracks cursor position within currentInput
	var lastCommand string
	var escState int  // State machine for escape sequences: 0=normal, 1=saw_esc, 2=saw_bracket
	var escSeq []byte // Buffer for escape sequence bytes

	// New helper to allow context override (for stacked commands)
	processCommandWithCtx := func(cmdStr string, useCtx context.Context) {
		// Per-connection command rate limiting.
		if info, ok := i.connections.Load(conn); ok {
			connInfo := info.(ConnectionInfo)
			if connInfo.CmdRateLimiter != nil && !connInfo.CmdRateLimiter.Take() {
				i.writeBaudf(conn, writer, "\r\nRate limit exceeded. Slow down.\r\n")
				return
			}
		}
		// Get player info for the task
		var playerID string
		var galaxy uint16
		if info, ok := i.connections.Load(conn); ok {
			connInfo := info.(ConnectionInfo)
			playerID = connInfo.Shipname
			galaxy = connInfo.Galaxy
			if playerID == "" {
				playerID = connInfo.IP // Use IP as fallback for pregame
			}
		}

		// Create response channel
		response := make(chan string, 1)

		// Create game task
		task := &GameTask{
			PlayerID: playerID,
			Command:  cmdStr,
			Galaxy:   galaxy,
			Conn:     conn,
			Writer:   writer,
			Context:  useCtx,
			Response: response,
		}

		// Route command to appropriate processor
		if i.isGameStateChangingCommand(cmdStr) {
			// Game-state-changing commands go through the per-galaxy command queue
			galaxyObj := i.getOrCreateGalaxy(galaxy)
			task.IsStateChanging = true
			log.Printf("Routing game-state-changing command '%s' to galaxy %d queue for player %s", cmdStr, galaxy, playerID)
			enqueueCtx, enqueueCancel := context.WithTimeout(useCtx, galaxyEnqueueTimeout)
			select {
			case galaxyObj.CommandQueue <- task:
				enqueueCancel()
				// Wait for response and output it
				go func() {
					// Select on both response and context cancellation to
					// prevent this goroutine from leaking when the connection
					// drops while the task is still queued or executing.
					// The response channel is buffered (size 1), so the
					// processor's eventual send will never block even after
					// we have returned here.
					select {
					case result := <-response:
						if result != "" {
							i.writeBaudfCtx(useCtx, conn, writer, "\r\n%s\r\n", result)
						}

						// Re-render prompt after command completes
						prompt := i.getPrompt(conn)
						if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
							mutex := mutexRaw.(*sync.Mutex)
							mutex.Lock()
							fmt.Fprintf(writer, "\r%-79s\r%s", "", prompt)
							writer.Flush()
							mutex.Unlock()
						}
					case <-useCtx.Done():
						// Connection closed or timed out; discard the result.
						// The buffered channel absorbs the processor's send.
					}
				}()
			case <-useCtx.Done():
				enqueueCancel()
				// Context cancelled, don't process
				return
			case <-enqueueCtx.Done():
				enqueueCancel()
				// Galaxy engine did not drain within timeout — tell the player.
				i.writeBaudfCtx(useCtx, conn, writer,
					"\r\nGalaxy %d engine busy; command '%s' could not be queued after %s — please try again.\r\n",
					galaxy, cmdStr, galaxyEnqueueTimeout)
			}
		} else {
			// Non-state-changing commands use per-ship processor for better performance
			log.Printf("Routing non-state-changing command '%s' to per-ship processor for player %s", cmdStr, playerID)
			start := time.Now()
			if info, ok := i.connections.Load(conn); ok {
				connInfo := info.(ConnectionInfo)
				if connInfo.CommandQueue == nil {
					connInfo.CommandQueue = make(chan *GameTask, 10)
					i.startShipCommandProcessor(conn, &connInfo)
					i.connections.Store(conn, connInfo)
				}
				enqueueCtx, enqueueCancel := context.WithTimeout(useCtx, galaxyEnqueueTimeout)
				select {
				case connInfo.CommandQueue <- task:
					enqueueCancel()
					// Wait for response and output it
					go func(cmdStr string, playerID string, start time.Time) {
						// Same pattern as the galaxy queue branch: select on
						// both the response and context cancellation to avoid
						// leaking this goroutine when the connection drops
						// while the command is still in-flight.
						select {
						case result := <-response:
							elapsed := time.Since(start).Nanoseconds()
							log.Printf("Non-state-changing command '%s' for player %s completed in %d ns", cmdStr, playerID, elapsed)
							if result != "" {
								i.writeBaudfCtx(useCtx, conn, writer, "\r\n%s\r\n", result)
							}

							// Re-render prompt after command completes
							prompt := i.getPrompt(conn)
							if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
								mutex := mutexRaw.(*sync.Mutex)
								mutex.Lock()
								fmt.Fprintf(writer, "\r%-79s\r%s", "", prompt)
								writer.Flush()
								mutex.Unlock()
							}
						case <-useCtx.Done():
							// Connection closed; discard result. Buffered channel
							// means the processor send will not block.
						}
					}(cmdStr, playerID, start)
				case <-useCtx.Done():
					enqueueCancel()
					// Context cancelled, don't process
					return
				case <-enqueueCtx.Done():
					enqueueCancel()
					// Ship processor did not drain within timeout — tell the player.
					i.writeBaudfCtx(useCtx, conn, writer,
						"\r\nServer busy; command '%s' could not be queued after %s — please try again.\r\n",
						cmdStr, galaxyEnqueueTimeout)
				}
			}
		}
	}

	// Helper function to send command to appropriate processor
	processCommand := func(cmdStr string) {
		processCommandWithCtx(cmdStr, ctx)
	}

	for {
		// Do not print the prompt here; it will be printed after command processing
		// Do not redraw the buffer for printable characters; only for editing commands.

		char, err := reader.ReadByte()
		if err != nil {
			// An error, such as io.EOF, indicates the connection is closed.
			// Cancel context and return to allow deferred cleanup functions to run.
			cancel()
			return
		}

		// Robust Telnet negotiation handling
		if char == IAC {
			cmd, err := reader.ReadByte()
			if err != nil {
				continue
			}
			switch cmd {
			case AYT:
				if writerRaw, ok := i.writers.Load(conn); ok {
					writer := writerRaw.(*bufio.Writer)
					i.writeBaudf(conn, writer, "[Yes]\r\n")
				}
				continue
			case SIGQUIT:
				if writerRaw, ok := i.writers.Load(conn); ok {
					writer := writerRaw.(*bufio.Writer)
					i.writeBaudf(conn, writer, "\r\nReceived SIGQUIT. Goodbye.\r\n")
				}
				return
			case DO, DONT, WILL, WONT:
				_, err := reader.ReadByte()
				if err != nil {
					continue
				}
				continue
			default:
				_, err := reader.ReadByte()
				if err != nil {
					continue
				}
				continue
			}
		}

		// State machine approach for escape sequences with peek-ahead for arrow keys
		switch escState {
		case 0: // Normal state
			if char == ESC {
				// Check if we can peek ahead to see if this is an arrow key sequence
				conn.SetReadDeadline(time.Now().Add(50 * time.Millisecond))
				nextByte, err := reader.ReadByte()
				conn.SetReadDeadline(time.Time{}) // Clear deadline

				if err != nil {
					// Timeout or no data - treat as standalone ESC
					prefix := currentInput.String()
					if prefix != "" {
						// Command completion
						processCommand("ESC_COMPLETE:" + prefix)
					} else if lastCommand != "" {
						// Prompt the repeated command line before processing
						prompt := i.getPrompt(conn)
						if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
							mutex := mutexRaw.(*sync.Mutex)
							mutex.Lock()
							fmt.Fprintf(writer, "\r%s%s\r\n", prompt, lastCommand)
							writer.Flush()
							mutex.Unlock()
						}
						// Process repeated commands using proper chaining
						if strings.Contains(lastCommand, "/") {
							// Use ExecuteCombined for proper sequential processing
							i.ExecuteCombined(lastCommand, conn, writer, ctx)
						} else {
							cmdStr := strings.TrimSpace(lastCommand)
							if cmdStr != "" {
								processCommand(cmdStr)
							}
						}
					}
					continue
				}

				if nextByte == '[' {
					// Start of arrow key sequence
					escState = 2
					escSeq = []byte{ESC, '['}
					continue
				} else {
					// ESC followed by something else - process ESC as standalone
					prefix := currentInput.String()
					if prefix != "" {
						// Command completion
						processCommand("ESC_COMPLETE:" + prefix)
					} else if lastCommand != "" {
						// Prompt the repeated command line before processing
						prompt := i.getPrompt(conn)
						if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
							mutex := mutexRaw.(*sync.Mutex)
							mutex.Lock()
							fmt.Fprintf(writer, "\r%s%s\r\n", prompt, lastCommand)
							writer.Flush()
							mutex.Unlock()
						}
						// Process repeated commands using proper chaining
						if strings.Contains(lastCommand, "/") {
							// Use ExecuteCombined for proper sequential processing
							i.ExecuteCombined(lastCommand, conn, writer, ctx)
						} else {
							cmdStr := strings.TrimSpace(lastCommand)
							if cmdStr != "" {
								processCommand(cmdStr)
							}
						}
					}
					// Process the next byte normally
					char = nextByte
				}
			}
		case 1: // Just saw ESC - no longer used with peek-ahead approach
		case 2: // Saw ESC [
			escSeq = append(escSeq, char)
			if char == 'A' || char == 'B' || char == 'C' || char == 'D' {
				// Arrow keys
				if info, ok := i.connections.Load(conn); ok {
					connInfo := info.(ConnectionInfo)
					switch char {
					case 'A': // Up arrow
						if len(connInfo.CommandHistory) > 0 && connInfo.HistoryIndex > 0 {
							connInfo.HistoryIndex--
							currentInput.Reset()
							currentInput.WriteString(connInfo.CommandHistory[connInfo.HistoryIndex])
							cursorPos = currentInput.Len()
							prompt := i.getPrompt(conn)
							if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
								mutex := mutexRaw.(*sync.Mutex)
								mutex.Lock()
								fmt.Fprintf(writer, "\033[2K\r%s%s", prompt, currentInput.String())
								writer.Flush()
								mutex.Unlock()
							}
						}
					case 'B': // Down arrow
						if len(connInfo.CommandHistory) > 0 && connInfo.HistoryIndex < len(connInfo.CommandHistory)-1 {
							connInfo.HistoryIndex++
							currentInput.Reset()
							currentInput.WriteString(connInfo.CommandHistory[connInfo.HistoryIndex])
							cursorPos = currentInput.Len()
							prompt := i.getPrompt(conn)
							if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
								mutex := mutexRaw.(*sync.Mutex)
								mutex.Lock()
								fmt.Fprintf(writer, "\033[2K\r%s%s", prompt, currentInput.String())
								writer.Flush()
								mutex.Unlock()
							}
						} else if connInfo.HistoryIndex == len(connInfo.CommandHistory)-1 {
							connInfo.HistoryIndex++
							currentInput.Reset()
							cursorPos = 0
							prompt := i.getPrompt(conn)
							if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
								mutex := mutexRaw.(*sync.Mutex)
								mutex.Lock()
								fmt.Fprintf(writer, "\033[2K\r%s", prompt)
								writer.Flush()
								mutex.Unlock()
							}
						}
					case 'C': // Right arrow
						if cursorPos < currentInput.Len() {
							cursorPos++
							prompt := i.getPrompt(conn)
							if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
								mutex := mutexRaw.(*sync.Mutex)
								mutex.Lock()
								fmt.Fprintf(writer, "\033[2K\r%s%s", prompt, currentInput.String())
								fmt.Fprintf(writer, "\033[%dG", len(prompt)+cursorPos+1)
								writer.Flush()
								mutex.Unlock()
							}
						}
					case 'D': // Left arrow
						if cursorPos > 0 {
							cursorPos--
							prompt := i.getPrompt(conn)
							if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
								mutex := mutexRaw.(*sync.Mutex)
								mutex.Lock()
								fmt.Fprintf(writer, "\033[2K\r%s%s", prompt, currentInput.String())
								fmt.Fprintf(writer, "\033[%dG", len(prompt)+cursorPos+1)
								writer.Flush()
								mutex.Unlock()
							}
						}
					}
					i.connections.Store(conn, connInfo)
				}
				escState = 0
				escSeq = nil
				continue
			} else if char == '3' && len(escSeq) == 3 {
				// ESC [ 3 - might be delete key, wait for ~
				continue
			} else if char == '~' && len(escSeq) == 4 && escSeq[2] == '3' {
				// Delete key: ESC [ 3 ~
				if cursorPos < currentInput.Len() {
					inputRunes := []rune(currentInput.String())
					inputRunes = append(inputRunes[:cursorPos], inputRunes[cursorPos+1:]...)
					currentInput.Reset()
					currentInput.WriteString(string(inputRunes))
					prompt := i.getPrompt(conn)
					if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
						mutex := mutexRaw.(*sync.Mutex)
						mutex.Lock()
						fmt.Fprintf(writer, "\033[2K\r%s%s", prompt, currentInput.String())
						fmt.Fprintf(writer, "\033[%dG", len(prompt)+cursorPos+1)
						writer.Flush()
						mutex.Unlock()
					}
				}
				escState = 0
				escSeq = nil
				continue
			} else if char == ESC {
				// New ESC while in bracket sequence - abandon current and start new
				escState = 1
				escSeq = []byte{ESC}
				continue
			} else {
				// Unknown sequence - abandon it
				escState = 0
				escSeq = nil
				continue
			}
		}

		// Reset escape state if we get here with a normal character
		if escState != 0 {
			escState = 0
			escSeq = nil
		}

		// Update last activity time
		if info, ok := i.connections.Load(conn); ok {
			connInfo := info.(ConnectionInfo)
			connInfo.LastActivity = time.Now()
			i.connections.Store(conn, connInfo)
		}

		// Handle telnet IAC sequences
		if char == IAC {
			cmd, err := reader.ReadByte()
			if err != nil {
				continue
			}
			switch cmd {
			case AYT:
				i.writeBaudf(conn, writer, "[Yes]\r\n")
				continue
			case SIGQUIT:
				i.writeBaudf(conn, writer, "\r\nReceived SIGQUIT. Goodbye.\r\n")
				return
			case DO, DONT, WILL, WONT:
				_, err := reader.ReadByte()
				if err != nil {
					continue
				}
				continue
			default:
				_, err := reader.ReadByte()
				if err != nil {
					continue
				}
				continue
			}
		}

		// Process control and printable characters
		if char < 32 || char == 127 {
			switch char {
			case '\r', '\n', 8, 127, 9, 11, 21, 23, 2, 3, 6, 12, 1, 5, 4: // Add Ctrl+B (2), Ctrl+C (3), Ctrl+F (6), Ctrl+L (12) Ctrl+D (removed ESC)
				if char == 3 { // Ctrl-C
					// Create new context to cancel current command
					newCtx, newCancel := context.WithCancel(context.Background())
					cancel() // Interrupt running command - this will cause writeBaudfCtx to show [Output interrupted]

					// Replace context and cancel function
					ctx = newCtx
					cancel = newCancel

					currentInput.Reset()
					cursorPos = 0

					// Show immediate prompt
					prompt := i.getPrompt(conn)
					if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
						mutex := mutexRaw.(*sync.Mutex)
						mutex.Lock()
						fmt.Fprintf(writer, "\r\n%s", prompt)
						writer.Flush()
						mutex.Unlock()
					}
					continue
				}
				if char == 8 || char == 127 { // Backspace (ASCII 8 or 127)
					if cursorPos > 0 {
						inputRunes := []rune(currentInput.String())
						inputRunes = append(inputRunes[:cursorPos-1], inputRunes[cursorPos:]...)
						currentInput.Reset()
						currentInput.WriteString(string(inputRunes))
						cursorPos--
						prompt := i.getPrompt(conn)
						if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
							mutex := mutexRaw.(*sync.Mutex)
							mutex.Lock()
							fmt.Fprintf(writer, "\033[2K\r%s%s", prompt, currentInput.String())
							fmt.Fprintf(writer, "\033[%dG", len(prompt)+cursorPos+1)
							writer.Flush()
							mutex.Unlock()
						}
					}
					continue
				}
				// Allowed control characters
			default:
				continue
			}
		} else if char > 127 {
			continue
		}

		section := "pregame"
		if info, ok := i.connections.Load(conn); ok {
			connInfo := info.(ConnectionInfo)
			section = connInfo.Section
			if connInfo.Section == "gowars" {
				i.trackerMutex.Lock()
				if tracker, exists := i.galaxyTracker[connInfo.Galaxy]; exists {
					tracker.LastActive = time.Now()
					i.galaxyTracker[connInfo.Galaxy] = tracker
				} else {
					now := time.Now()
					i.galaxyTracker[connInfo.Galaxy] = GalaxyTracker{GalaxyStart: now, LastActive: now}
				}
				i.trackerMutex.Unlock()
			}
		}

		switch char {
		case '?':
			prefix := currentInput.String()
			if prefix == "" {
				handler := i.pregameCommands["help"].Handler
				if section == "gowars" {
					handler = i.gowarsCommands["help"].Handler
				}
				// Run help output in a goroutine with context for interruption
				go func(ctx context.Context) {
					result := handler([]string{}, conn)
					i.writeBaudfCtx(ctx, conn, writer, "\r\n%s\r\n", result)
					// Redraw prompt and empty input
					prompt := i.getPrompt(conn)
					if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
						mutex := mutexRaw.(*sync.Mutex)
						mutex.Lock()
						fmt.Fprintf(writer, "%s", prompt)
						writer.Flush()
						mutex.Unlock()
					}
				}(ctx)
				continue // Don't block main loop
			} else {
				// Split on '/' to get the last command segment
				segments := strings.Split(prefix, "/")
				lastSegment := segments[len(segments)-1]
				trimmedLast := strings.TrimSpace(lastSegment)
				// If last segment is a known command, prompt for its parameters
				fullCmd, ok := i.resolveCommand(trimmedLast, section)
				if ok {
					completions := i.getCompletions(fullCmd+" ", section, conn)
					if len(completions) > 0 {
						i.writeBaudf(conn, writer, "\r\n%s\r\n", strings.Join(completions, "\r\n"))
						prompt := i.getPrompt(conn)
						if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
							mutex := mutexRaw.(*sync.Mutex)
							mutex.Lock()
							fmt.Fprintf(writer, "%s%s", prompt, prefix)
							writer.Flush()
							mutex.Unlock()
						}
					} else {
						// Special handling for tractor command parameter prompt
						if fullCmd == "tractor" {
							var completions []string
							completions = append(completions, "tractor")
							completions = append(completions, "tractor off")
							// List all ships in the galaxy
							for _, obj := range i.objects {
								if obj.Type == "Ship" {
									completions = append(completions, fmt.Sprintf("tractor %s", obj.Name))
								}
							}
							i.writeBaudf(conn, writer, "\r\n%s\r\n", strings.Join(completions, "\r\n"))
						} else {
							// Special handling for targets command parameter prompt
							if fullCmd == "targets" {
								i.writeBaudf(conn, writer, "\r\ntargets <radius>\r\n")
							} else if fullCmd == "activate" {
								i.writeBaudf(conn, writer, "\r\n"+
									"  Side                    - fed/federation or emp/empire (optional)\r\n"+
									"  Galaxy                  - 0-19 (default: 0)\r\n"+
									"  DecwarMode              - True/False\r\n"+
									"  MaxSizeX                - 21-99 (default: 75, 75)\r\n"+
									"  MaxSizeY                - 21-99 (default: 75, 75)\r\n"+
									"  MaxRomulans             - 0-9999\r\n"+
									"  MaxBlackHoles           - 0-9999\r\n"+
									"  MaxNeutralPlanets       - 0-9999\r\n"+
									"  MaxFederationPlanets    - 0-9999\r\n"+
									"  MaxEmpirePlanets        - 0-9999\r\n"+
									"  MaxStars                - 0-9999\r\n"+
									"  MaxBasesPerSide         - 0-9999\r\n"+
									"\r\nAll parameters are required if you enter parameters, the sum of objects < 10000:\r\n")
							} else if fullCmd == "admin" {
								i.writeBaudf(conn, writer, "\r\n%s\r\n", adminHelpText)
							} else {
								i.writeBaudf(conn, writer, "\r\nNo parameters for command: %s\r\n", fullCmd)
							}
						}
						prompt := i.getPrompt(conn)
						if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
							mutex := mutexRaw.(*sync.Mutex)
							mutex.Lock()
							fmt.Fprintf(writer, "%s%s", prompt, prefix)
							writer.Flush()
							mutex.Unlock()
						}
					}
				} else {
					// Otherwise, try to complete the last segment as before
					inputWithQuestion := trimmedLast + "?"
					completions := i.getCompletions(inputWithQuestion, section, conn)
					switch len(completions) {
					case 0:
						i.writeBaudf(conn, writer, "\r\nInvalid input: '%s'\r\n", trimmedLast)
						prompt := i.getPrompt(conn)
						if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
							mutex := mutexRaw.(*sync.Mutex)
							mutex.Lock()
							fmt.Fprintf(writer, "%s%s", prompt, prefix)
							writer.Flush()
							mutex.Unlock()
						}
					case 1:
						segments[len(segments)-1] = completions[0] + " "
						newInput := strings.Join(segments, "/")
						currentInput.Reset()
						currentInput.WriteString(newInput)
						cursorPos = len(newInput)
						prompt := i.getPrompt(conn)
						if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
							mutex := mutexRaw.(*sync.Mutex)
							mutex.Lock()
							fmt.Fprintf(writer, "\r%s%s", prompt, newInput)
							writer.Flush()
							mutex.Unlock()
						}
					default:
						i.writeBaudf(conn, writer, "\r\n%s\r\n", strings.Join(completions, "\r\n"))
						prompt := i.getPrompt(conn)
						if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
							mutex := mutexRaw.(*sync.Mutex)
							mutex.Lock()
							fmt.Fprintf(writer, "%s%s", prompt, prefix)
							writer.Flush()
							mutex.Unlock()
						}
					}
				}
			}

		// ESC is now handled by state machine above, removed from here

		case '\r', '\n':
			// Do not clear the input line; just send CR/LF to the client
			if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
				mutex := mutexRaw.(*sync.Mutex)
				mutex.Lock()
				writer.WriteString("\r\n")
				writer.Flush()
				mutex.Unlock()
			}
			if currentInput.Len() == 0 {
				// If input is empty, just reprompt
				prompt := i.getPrompt(conn)
				if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
					mutex := mutexRaw.(*sync.Mutex)
					mutex.Lock()
					fmt.Fprintf(writer, "%s", prompt)
					writer.Flush()
					mutex.Unlock()
				}
				continue
			}
			if currentInput.Len() > 0 {
				command := currentInput.String()
				lastCommand = command

				// Check if this is a chained command (contains "/")
				if strings.Contains(command, "/") {
					// Use ExecuteCombined for proper sequential processing
					i.ExecuteCombined(command, conn, writer, ctx)
				} else {
					// Single command - use existing processCommand
					processCommand(strings.TrimSpace(command))
				}

				// Add to command history
				if info, ok := i.connections.Load(conn); ok {
					connInfo := info.(ConnectionInfo)
					if currentInput.Len() > 0 {
						cmd := currentInput.String()
						// Avoid duplicate consecutive entries
						if len(connInfo.CommandHistory) == 0 || connInfo.CommandHistory[len(connInfo.CommandHistory)-1] != cmd {
							connInfo.CommandHistory = append(connInfo.CommandHistory, cmd)
						}
						connInfo.HistoryIndex = len(connInfo.CommandHistory)
						i.connections.Store(conn, connInfo)
					}
				}

				currentInput.Reset() // Clear buffer after processing command
				cursorPos = 0        // Reset cursor position
			}

		case 4: // Ctrl+D (EOF)
			if currentInput.Len() > 0 {
				command := currentInput.String()
				lastCommand = command

				// Check if this is a chained command (contains "/")
				if strings.Contains(command, "/") {
					// Use ExecuteCombined for proper sequential processing
					i.ExecuteCombined(command, conn, writer, ctx)
				} else {
					// Single command - use existing processCommand
					processCommand(strings.TrimSpace(command))
				}
				currentInput.Reset() // Clear buffer after processing command
				cursorPos = 0        // Reset cursor position
			}
			cancel() // Cancel context on EOF
			return

		case 8, 127: // Backspace or Delete
			if cursorPos > 0 {
				inputStr := currentInput.String()
				//      oldLen := len(inputStr)
				newInput := inputStr[:cursorPos-1] + inputStr[cursorPos:]
				currentInput.Reset()
				currentInput.WriteString(newInput)
				cursorPos--
				prompt := i.getPrompt(conn)
				fmt.Fprintf(writer, "\r%s%s", prompt, newInput)
				// Erase leftover from old line (always 1 char for backspace)
				fmt.Fprintf(writer, " ")
				// Redraw clean line
				fmt.Fprintf(writer, "\r%s%s", prompt, newInput)
				if cursorPos < len(newInput) {
					fmt.Fprintf(writer, "%s", strings.Repeat("\b", len(newInput)-cursorPos))
				}
				if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
					mutex := mutexRaw.(*sync.Mutex)
					mutex.Lock()
					writer.Flush()
					mutex.Unlock()
				}
			}
		case 21: // Ctrl+U (clear line)
			if currentInput.Len() > 0 {
				inputLen := currentInput.Len()
				prompt := i.getPrompt(conn)
				if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
					mutex := mutexRaw.(*sync.Mutex)
					mutex.Lock()
					fmt.Fprintf(writer, "\r%s", strings.Repeat(" ", len(prompt)+inputLen))
					fmt.Fprintf(writer, "\r%s", prompt)
					writer.Flush()
					mutex.Unlock()
				}
				currentInput.Reset()
				cursorPos = 0
			}

		case 23: // Ctrl+W (delete word)
			if cursorPos > 0 {
				inputStr := currentInput.String()
				oldLen := len(inputStr)
				// Find the last word boundary before cursor
				trimmed := inputStr[:cursorPos]
				lastSpace := strings.LastIndex(trimmed, " ")
				if lastSpace == -1 {
					lastSpace = 0
				}
				newInput := inputStr[:lastSpace] + inputStr[cursorPos:]
				currentInput.Reset()
				currentInput.WriteString(newInput)
				cursorPos = lastSpace
				prompt := i.getPrompt(conn)
				// Redraw prompt and new input, then clear leftover characters from old input
				fmt.Fprintf(writer, "\r%s%s", prompt, newInput)
				if oldLen > len(newInput) {
					fmt.Fprintf(writer, "%s", strings.Repeat(" ", oldLen-len(newInput)))
				}
				// Reposition cursor to correct location
				fmt.Fprintf(writer, "\r%s%s", prompt, newInput[:cursorPos])
				if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
					mutex := mutexRaw.(*sync.Mutex)
					mutex.Lock()
					writer.Flush()
					mutex.Unlock()
				}
			}

		case 11: // Ctrl+K (delete to end of line)
			if cursorPos < currentInput.Len() {
				inputStr := currentInput.String()
				newInput := inputStr[:cursorPos]
				currentInput.Reset()
				currentInput.WriteString(newInput)
				prompt := i.getPrompt(conn)
				if len(newInput) == 0 {
					// Entire line cleared, refresh with new prompt
					fmt.Fprintf(writer, "\r%s", strings.Repeat(" ", len(inputStr)))
					fmt.Fprintf(writer, "\r%s", prompt)
				} else {
					// Partial deletion, redraw prompt and remaining input, clear remainder
					fmt.Fprintf(writer, "\r%s%s", prompt, newInput)
					// Clear any leftover characters from previous input
					fmt.Fprintf(writer, "%s", strings.Repeat(" ", len(inputStr)-len(newInput)))
					// Move cursor back to correct position if needed
					fmt.Fprintf(writer, "\r%s%s", prompt, newInput)
					if cursorPos < len(newInput) {
						fmt.Fprintf(writer, "%s", strings.Repeat("\b", len(newInput)-cursorPos))
					}
				}
				if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
					mutex := mutexRaw.(*sync.Mutex)
					mutex.Lock()
					writer.Flush()
					mutex.Unlock()
				}
			}
		case 1: // Ctrl+A (move cursor to beginning of line)
			cursorPos = 0
			prompt := i.getPrompt(conn)
			if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
				mutex := mutexRaw.(*sync.Mutex)
				mutex.Lock()
				fmt.Fprintf(writer, "\r%s%s", prompt, currentInput.String())
				// Move cursor to beginning after prompt
				if currentInput.Len() > 0 {
					fmt.Fprintf(writer, "%s", strings.Repeat("\b", currentInput.Len()))
				}
				writer.Flush()
				mutex.Unlock()
			}

		case 5: // Ctrl+E (move cursor to end of line)
			cursorPos = currentInput.Len()
			prompt := i.getPrompt(conn)
			if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
				mutex := mutexRaw.(*sync.Mutex)
				mutex.Lock()
				fmt.Fprintf(writer, "\r%s%s", prompt, currentInput.String())
				// Cursor is already at end, no need to move
				writer.Flush()
				mutex.Unlock()
			}

		case 12: // Ctrl+L (clear screen)
			// Stub: Clear the terminal screen (actual implementation may vary by client)
			// Most terminals recognize "\033[2J\033[H" as clear screen and move cursor to home
			if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
				mutex := mutexRaw.(*sync.Mutex)
				mutex.Lock()
				fmt.Fprintf(writer, "\033[2J\033[H")
				prompt = i.getPrompt(conn)
				fmt.Fprintf(writer, "%s%s", prompt, currentInput.String())
				// Move cursor to correct position
				if cursorPos < currentInput.Len() {
					fmt.Fprintf(writer, "%s", strings.Repeat("\b", currentInput.Len()-cursorPos))
				}
				writer.Flush()
				mutex.Unlock()
			}

		case 9: // Tab
			prefix := currentInput.String()
			if prefix != "" {
				// Split on '/' to get the last command segment
				segments := strings.Split(prefix, "/")
				lastSegment := segments[len(segments)-1]
				completions := i.getCompletions(strings.TrimSpace(lastSegment), section, conn)
				switch len(completions) {
				case 0:
					i.writeBaudf(conn, writer, "\r\nInvalid input: '%s'\r\n", lastSegment)
					// Redraw prompt and current input
					prompt := i.getPrompt(conn)
					if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
						mutex := mutexRaw.(*sync.Mutex)
						mutex.Lock()
						fmt.Fprintf(writer, "%s%s", prompt, prefix)
						writer.Flush()
						mutex.Unlock()
					}
				case 1:
					// Inline completion for last segment only
					completed := completions[0] + " "
					segments[len(segments)-1] = completed
					newInput := strings.Join(segments, "/")
					oldLen := currentInput.Len()
					currentInput.Reset()
					currentInput.WriteString(newInput)
					cursorPos = len(newInput)
					prompt := i.getPrompt(conn)
					// Redraw line inline
					fmt.Fprintf(writer, "\r%s%s", prompt, newInput)
					// If previous input was longer, erase extra chars
					if len(newInput) < oldLen {
						extra := oldLen - len(newInput)
						fmt.Fprintf(writer, "%s", strings.Repeat(" ", extra))
						fmt.Fprintf(writer, "%s", strings.Repeat("\b", extra))
					}
					if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
						mutex := mutexRaw.(*sync.Mutex)
						mutex.Lock()
						writer.Flush()
						mutex.Unlock()
					}
				default:
					// Show possible completions for last segment, then redraw prompt and input
					i.writeBaudf(conn, writer, "\r\n%s\r\n", strings.Join(completions, "\r\n"))
					prompt := i.getPrompt(conn)
					if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
						mutex := mutexRaw.(*sync.Mutex)
						mutex.Lock()
						fmt.Fprintf(writer, "%s%s", prompt, prefix)
						writer.Flush()
						mutex.Unlock()
					}
				}
			}

		case 2: // Ctrl+B (cursor left)
			if cursorPos > 0 {
				cursorPos--
				if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
					mutex := mutexRaw.(*sync.Mutex)
					mutex.Lock()
					fmt.Fprintf(writer, "\b")
					writer.Flush()
					mutex.Unlock()
				}
			}

		case 6: // Ctrl+F (cursor right)
			if cursorPos < currentInput.Len() {
				cursorPos++
				if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
					mutex := mutexRaw.(*sync.Mutex)
					mutex.Lock()
					fmt.Fprintf(writer, "\x1b[C")
					writer.Flush()
					mutex.Unlock()
				}
			}

		default:
			if char >= 32 && char <= 126 {
				// Check input length limit to prevent memory exhaustion
				if currentInput.Len() >= MaxInputLength {
					// Silently ignore additional characters beyond the limit
					// Ring the bell to notify the user
					if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
						mutex := mutexRaw.(*sync.Mutex)
						mutex.Lock()
						writer.WriteByte(7) // ASCII bell character
						writer.Flush()
						mutex.Unlock()
					}
					continue
				}
				inputStr := currentInput.String()
				newInput := inputStr[:cursorPos] + string(char) + inputStr[cursorPos:]
				currentInput.Reset()
				currentInput.WriteString(newInput)
				cursorPos++
				if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
					mutex := mutexRaw.(*sync.Mutex)
					mutex.Lock()
					writer.WriteByte(char) // Echo only the typed character
					writer.Flush()
					mutex.Unlock()
				}
			}
		}
	}
}

func (i *Interpreter) getAbbreviation(cmd string, allCmds []string) string {
	for abbrLen := 1; abbrLen <= len(cmd); abbrLen++ {
		abbr := cmd[:abbrLen]
		count := 0
		for _, other := range allCmds {
			if strings.HasPrefix(other, abbr) {
				count++
			}
		}
		if count == 1 {
			// Capitalize the abbreviation, rest lowercase
			return strings.ToUpper(abbr) + cmd[abbrLen:]
		}
	}
	// Fallback: all caps
	return strings.ToUpper(cmd)
}

func (i *Interpreter) withinRange(shipX, shipY int, rangeLimit int, thetype string, mySide string, galaxy uint16) bool {
	// Get all objects of the specified type in the galaxy
	objects := i.getObjectsByType(galaxy, thetype)
	if objects == nil {
		return false
	}

	for _, obj := range objects {
		if obj.Side != mySide && obj.Side != "neutral" {
			if obj.LocationX >= shipX-rangeLimit && obj.LocationX <= shipX+rangeLimit &&
				obj.LocationY >= shipY-rangeLimit && obj.LocationY <= shipY+rangeLimit {
				return true
			}
		}
	}
	return false
}

type ObjectDetails struct {
	Type                 string `json:"type"`
	Name                 string `json:"name"`
	Side                 string `json:"side"`
	LocationX            int    `json:"locationX"`
	LocationY            int    `json:"locationY"`
	Shields              int    `json:"shields"`
	ShieldsDamage        int    `json:"shieldsDamage"`
	ShipEnergy           int    `json:"shipEnergy"`
	WarpEngines          int    `json:"warpEngines"`
	WarpEnginesDamage    int    `json:"warpEnginesDamage"`
	ImpulseEnginesDamage int    `json:"impulseEnginesDamage"`
	TorpedoTubes         int    `json:"torpedoTubes"`
	TorpedoTubeDamage    int    `json:"torpedoTubeDamage"`
	PhasersDamage        int    `json:"phasersDamage"`
	ComputerDamage       int    `json:"computerDamage"`
	LifeSupportDamage    int    `json:"lifeSupportDamage"`
	LifeSupportReserve   int    `json:"lifeSupportReserve"`
	RadioOnOff           bool   `json:"radioOnOff"`
	RadioDamage          int    `json:"radioDamage"`
	TractorOnOff         bool   `json:"tractorOnOff"`
	TractorShip          string `json:"tractorShip"`
	TractorDamage        int    `json:"tractorDamage"`
	Condition            string `json:"condition"`
	ShieldsUpDown        bool   `json:"shieldsUpDown"`
	TotalShipDamage      int    `json:"totalShipDamage"`
	StarDate             int    `json:"starDate"`
	DamageReport         string `json:"damageReport"`
}

type GalaxyData struct {
	ScanOutput string                   `json:"scanOutput"`
	Objects    map[string]ObjectDetails `json:"objects"`
	MaxSizeX   int                      `json:"maxSizeX"`
	MaxSizeY   int                      `json:"maxSizeY"`
}

func (i *Interpreter) getGalaxyData(galaxyID uint16, includeObjects bool) GalaxyData {
	// Default galaxy bounds
	actualMaxSizeX := MaxSizeX
	actualMaxSizeY := MaxSizeY

	// Try to get actual bounds from galaxyTracker
	i.trackerMutex.Lock()
	if tracker, exists := i.galaxyTracker[galaxyID]; exists {
		if tracker.MaxSizeX > 0 {
			actualMaxSizeX = tracker.MaxSizeX
		}
		if tracker.MaxSizeY > 0 {
			actualMaxSizeY = tracker.MaxSizeY
		}
	}
	i.trackerMutex.Unlock()

	// Use the exact same scan output as the telnet interface
	// scanShort = true, rangeWarn = false, full galaxy range
	scanOutput := i.outputScanCtxWithGalaxy(context.Background(), nil, galaxyID, true, false, BoardStart, BoardStart, actualMaxSizeX, actualMaxSizeY)

	// Collect object details for hover popups
	objects := make(map[string]ObjectDetails)
	if includeObjects {
		for r := BoardStart; r <= actualMaxSizeX; r++ {
			for c := BoardStart; c <= actualMaxSizeY; c++ {
				obj := i.getObjectAtLocation(galaxyID, r, c)
				if obj != nil {
					key := fmt.Sprintf("%d,%d", r, c)
					objects[key] = ObjectDetails{
						Type:                 obj.Type,
						Name:                 obj.Name,
						Side:                 obj.Side,
						LocationX:            obj.LocationX,
						LocationY:            obj.LocationY,
						Shields:              obj.Shields,
						ShieldsDamage:        obj.ShieldsDamage,
						ShipEnergy:           obj.ShipEnergy,
						WarpEngines:          obj.WarpEngines,
						WarpEnginesDamage:    obj.WarpEnginesDamage,
						ImpulseEnginesDamage: obj.ImpulseEnginesDamage,
						TorpedoTubes:         obj.TorpedoTubes,
						TorpedoTubeDamage:    obj.TorpedoTubeDamage,
						PhasersDamage:        obj.PhasersDamage,
						ComputerDamage:       obj.ComputerDamage,
						LifeSupportDamage:    obj.LifeSupportDamage,
						LifeSupportReserve:   obj.LifeSupportReserve,
						RadioOnOff:           obj.RadioOnOff,
						RadioDamage:          obj.RadioDamage,
						TractorOnOff:         obj.TractorOnOff,
						TractorShip:          obj.TractorShip,
						TractorDamage:        obj.TractorDamage,
						Condition:            obj.Condition,
						ShieldsUpDown:        obj.ShieldsUpDown,
						TotalShipDamage:      obj.TotalShipDamage,
						StarDate:             obj.StarDate,
						DamageReport:         formatDamageReportForObject(obj),
					}
				}
			}
		}
	}

	return GalaxyData{
		ScanOutput: scanOutput,
		Objects:    objects,
		MaxSizeX:   actualMaxSizeX,
		MaxSizeY:   actualMaxSizeY,
	}
}

// formatDamageReportForObject returns a formatted string of device damages for the given object.
func formatDamageReportForObject(obj *Object) string {
	if obj == nil {
		return ""
	}
	//	report := "Damage Report for " + obj.Name + "\n\n"
	report := "Device                  Damage\n"
	report += fmt.Sprintf("Deflector Shields:      %.1f units\n", float64(obj.ShieldsDamage))
	report += fmt.Sprintf("Warp Engines:           %.1f units\n", float64(obj.WarpEnginesDamage))
	report += fmt.Sprintf("Impulse Engines:        %.1f units\n", float64(obj.ImpulseEnginesDamage))
	report += fmt.Sprintf("Life Support:           %.1f units\n", float64(obj.LifeSupportDamage))
	report += fmt.Sprintf("Torpedo Tubes:          %.1f units\n", float64(obj.TorpedoTubeDamage))
	report += fmt.Sprintf("Phasers:                %.1f units\n", float64(obj.PhasersDamage))
	report += fmt.Sprintf("Computer:               %.1f units\n", float64(obj.ComputerDamage))
	report += fmt.Sprintf("Radio:                  %.1f units\n", float64(obj.RadioDamage))
	report += fmt.Sprintf("Tractor Beam:           %.1f units\n", float64(obj.TractorDamage))
	return report
}

func (i *Interpreter) startWebServer() {
	// HTML template for the galaxy display
	htmlTemplate := `
<!DOCTYPE html>
<html>
<head>
    <meta name="viewport" content="width=device-width, initial-scale=1.0, maximum-scale=5.0, user-scalable=yes">
    <title>GoWars God Mode</title>
    <link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/xterm@5.3.0/css/xterm.css" />
    <script src="https://cdn.jsdelivr.net/npm/xterm@5.3.0/lib/xterm.js"></script>
    <script src="https://cdn.jsdelivr.net/npm/xterm-addon-fit@0.8.0/lib/xterm-addon-fit.js"></script>
    <style>
        * { box-sizing: border-box; }
        html, body {
            margin: 0; padding: 0; height: 100%;
            font-family: monospace; background: #111; color: #ccc;
            overflow: hidden;
        }
        #page-header {
            display: flex;
            align-items: center;
            gap: 12px;
            padding: 6px 12px;
            background: #1a1a1a;
            border-bottom: 1px solid #333;
            flex-shrink: 0;
        }
        #page-header h1 { margin: 0; font-size: 16px; color: #0f0; white-space: nowrap; }
        #page-header .controls { display: flex; align-items: center; gap: 8px; flex-wrap: wrap; }
        #page-header label { color: #aaa; font-size: 13px; }
        #page-header select, #page-header button {
            font-size: 16px; padding: 3px 8px;
            background: #222; color: #0f0; border: 1px solid #555;
        }
        #page-header button:hover { background: #333; cursor: pointer; }
        #status { font-size: 12px; color: #888; margin-left: auto; white-space: nowrap; }

        /* Split pane layout */
        #split-container {
            display: flex;
            width: 100%;
            height: calc(100vh - 42px);
            overflow: hidden;
        }
        .pane {
            width: 50%;
            display: flex;
            flex-direction: column;
            overflow: hidden;
            outline: none;
            border: 2px solid transparent;
            transition: border-color 0.15s;
        }
        .pane:focus, .pane.focused {
            border-color: #0f0;
        }
        .pane-header {
            background: #1a1a1a;
            border-bottom: 1px solid #333;
            padding: 4px 10px;
            font-size: 12px;
            color: #888;
            flex-shrink: 0;
            user-select: none;
        }
        #divider {
            width: 4px;
            background: #333;
            cursor: col-resize;
            flex-shrink: 0;
            transition: background 0.15s;
        }
        #divider:hover { background: #0f0; }

        /* Galaxy pane */
        #galaxy-pane { }
        .galaxy-scroll-wrapper {
            overflow-x: auto;
            overflow-y: auto;
            -webkit-overflow-scrolling: touch;
            flex: 1;
            min-height: 0;
            scrollbar-width: thin;
            scrollbar-color: #444 #1a1a1a;
        }
        .galaxy-scroll-wrapper::-webkit-scrollbar { width: 8px; height: 8px; }
        .galaxy-scroll-wrapper::-webkit-scrollbar-track { background: #1a1a1a; }
        .galaxy-scroll-wrapper::-webkit-scrollbar-thumb { background: #444; border-radius: 4px; }
        .galaxy-grid {
            border: none;
            display: inline-block;
            background: black;
            color: lime;
            padding: 10px;
            font-size: 12px;
            line-height: 14px;
            white-space: pre;
            font-family: monospace;
            position: relative;
        }

        /* Telnet pane */
        #telnet-pane { }
        #telnet-toolbar {
            display: flex;
            align-items: center;
            gap: 8px;
            padding: 4px 8px;
            background: #1a1a1a;
            border-bottom: 1px solid #333;
            flex-shrink: 0;
        }
        #telnet-status { font-size: 12px; color: #ff0; flex: 1; }
        #reconnect-btn {
            font-size: 12px; padding: 2px 10px;
            background: #222; color: #0f0; border: 1px solid #0f0;
            cursor: pointer;
        }
        #reconnect-btn:hover { background: #0f0; color: #000; }
        /* Mobile keyboard toggle button in telnet toolbar */
        #mobile-kb-btn {
            display: none;
            font-size: 12px; padding: 2px 8px;
            background: #222; color: #0f0; border: 1px solid #0f0;
            cursor: pointer;
        }
        #mobile-kb-btn:hover { background: #0f0; color: #000; }
        /* Floating input bar for mobile soft-keyboard access */
        #mobile-input-bar {
            display: none;
            position: fixed;
            bottom: 0; left: 0; right: 0;
            background: #1a1a1a;
            border-top: 1px solid #444;
            padding: 6px 8px;
            z-index: 3000;
            gap: 6px;
            align-items: center;
        }
        #mobile-input-bar input {
            flex: 1;
            background: #000; color: #0f0;
            border: 1px solid #444;
            font-family: monospace;
            /* 16px prevents iOS Safari auto-zoom on focus */
            font-size: 16px;
            padding: 6px 8px;
            border-radius: 3px;
        }
        #mobile-input-bar button {
            background: #222; color: #0f0; border: 1px solid #0f0;
            font-size: 14px; padding: 6px 14px;
            border-radius: 3px; cursor: pointer; white-space: nowrap;
        }
        #mobile-input-bar button:active { background: #0f0; color: #000; }
        /* Tab bar (hidden on desktop) */
        #tab-bar {
            display: none;
        }
        #tab-bar button {
            flex: 1;
            padding: 8px 0;
            background: transparent; color: #888;
            border: none; border-bottom: 3px solid transparent;
            font-family: monospace; font-size: 13px; cursor: pointer;
        }
        #tab-bar button.active { color: #0f0; border-bottom-color: #0f0; }
        #terminal-wrapper {
            flex: 1;
            min-height: 0;
            overflow: hidden;
            display: flex;
            flex-direction: column;
        }
        #terminal-container {
            flex: 1;
            min-height: 0;
            min-width: 0;
        }

        /* Object popup */
        .object-popup {
            position: absolute;
            background: #222;
            border: 2px solid #555;
            padding: 10px;
            font-family: monospace;
            font-size: 11px;
            color: #fff;
            z-index: 1000;
            max-width: 300px;
            white-space: pre;
            box-shadow: 0 4px 8px rgba(0,0,0,0.5);
            pointer-events: none;
        }
        .object-popup .header {
            color: #4f4;
            font-weight: bold;
            border-bottom: 1px solid #555;
            margin-bottom: 5px;
            padding-bottom: 3px;
        }
        .object-popup .damage { color: #f44; }
        .object-popup .good   { color: #4f4; }
        .object-popup .warning{ color: #ff4; }

        /* Mobile */
        @media (max-width: 768px) {
            /* Show tab bar; hide divider */
            #tab-bar { display: flex; background: #111; border-bottom: 1px solid #333; flex-shrink: 0; }
            #divider { display: none; }
            /* Full-screen panes toggled by JS */
            #split-container { flex-direction: column; height: auto; flex: 1; }
            .pane { width: 100%; flex: 1; display: none; }
            .pane.tab-active { display: flex; }
            /* Header tidying */
            #page-header { flex-wrap: wrap; }
            #status { width: 100%; text-align: right; font-size: 11px; }
            #page-header h1 { font-size: 13px; }
            /* Galaxy grid */
            .galaxy-grid { font-size: 10px; line-height: 12px; padding: 6px; }
            /* Popup anchored to bottom */
            .object-popup {
                position: fixed;
                left: 5% !important; top: auto !important;
                bottom: 10px; right: 5%;
                max-width: 90%; width: 90%;
                font-size: 12px;
                pointer-events: auto;
                z-index: 2000;
            }
            /* Show mobile controls */
            #mobile-input-bar { display: flex; }
            #mobile-kb-btn { display: inline-block; }
            /* Pad telnet pane so content isn't hidden behind input bar */
            #telnet-pane { padding-bottom: 52px; }
        }
        @media (max-width: 480px) {
            .galaxy-grid { font-size: 8px; line-height: 10px; padding: 4px; }
            .object-popup { font-size: 11px; }
        }
    </style>
</head>
<body>
    <div id="page-header">
        <h1>GoWars God mode</h1>
        <div class="controls">
            <label for="galaxy-select">Galaxy:</label>
            <select id="galaxy-select">
                {{range $i := .Galaxies}}
                <option value="{{$i}}">Galaxy {{$i}}</option>
                {{end}}
            </select>
            <button onclick="refreshData()">Refresh Now</button>
        </div>
        <div id="status">Loading...</div>
    </div>

    <!-- Mobile tab bar (hidden on desktop via CSS) -->
    <div id="tab-bar">
        <button id="tab-galaxy" class="active" onclick="switchTab('galaxy')">&#128506; Galaxy</button>
        <button id="tab-telnet" onclick="switchTab('telnet')">&#128225; Terminal</button>
    </div>

    <div id="split-container">
        <!-- Galaxy chart pane -->
        <div class="pane" id="galaxy-pane" tabindex="0">
            <div class="pane-header">Galaxy Chart</div>
            <div class="galaxy-scroll-wrapper" id="galaxy-scroll">
                <div class="galaxy-grid" id="galaxy-grid"></div>
            </div>
        </div>

        <div id="divider"></div>

        <!-- Telnet client pane -->
        <div class="pane" id="telnet-pane" tabindex="0">
            <div id="telnet-toolbar">
                <span id="telnet-status">Connecting...</span>
                <button id="mobile-kb-btn" onclick="toggleMobileInput()" title="Toggle keyboard input">&#9000;</button>
                <button id="reconnect-btn" onclick="reconnectTelnet()">Reconnect</button>
            </div>
            <div id="terminal-wrapper">
                <div id="terminal-container"></div>
            </div>
        </div>
    </div>

    <!-- Floating input bar for mobile soft-keyboard -->
    <div id="mobile-input-bar">
        <input id="mobile-cmd-input" type="text" autocomplete="off" autocorrect="off"
               autocapitalize="off" spellcheck="false" placeholder="type command...">
        <button onclick="sendMobileInput()">Send</button>
        <button onclick="sendKey('\r')">Enter</button>
        <button onclick="hideMobileInput()">X</button>
    </div>

    <div class="object-popup" id="object-popup" style="display: none;"></div>

    <script>
        // ── Tab switching (mobile only) ──────────────────────────────────────
        function switchTab(which) {
            var galaxyPane = document.getElementById('galaxy-pane');
            var telnetPane = document.getElementById('telnet-pane');
            var tabG = document.getElementById('tab-galaxy');
            var tabT = document.getElementById('tab-telnet');
            if (which === 'galaxy') {
                galaxyPane.classList.add('tab-active');
                telnetPane.classList.remove('tab-active');
                tabG.classList.add('active');
                tabT.classList.remove('active');
            } else {
                telnetPane.classList.add('tab-active');
                galaxyPane.classList.remove('tab-active');
                tabT.classList.add('active');
                tabG.classList.remove('active');
                // Refit xterm now that its container is visible
                if (typeof fitAddon !== 'undefined') {
                    setTimeout(function() { fitAddon.fit(); }, 50);
                }
            }
        }
        // On mobile, default galaxy pane to active
        if (window.innerWidth <= 768) {
            document.getElementById('galaxy-pane').classList.add('tab-active');
        }

        // ── Mobile input bar helpers ─────────────────────────────────────────
        function sendKey(key) {
            if (ws && ws.readyState === WebSocket.OPEN) { ws.send(key); }
        }
        function sendMobileInput() {
            var inp = document.getElementById('mobile-cmd-input');
            var text = inp.value;
            if (text && ws && ws.readyState === WebSocket.OPEN) {
                ws.send(text + '\r');
                inp.value = '';
            }
        }
        function toggleMobileInput() {
            var bar = document.getElementById('mobile-input-bar');
            var visible = (bar.style.display === 'flex');
            bar.style.display = visible ? 'none' : 'flex';
            if (!visible) { document.getElementById('mobile-cmd-input').focus(); }
        }
        function hideMobileInput() {
            document.getElementById('mobile-input-bar').style.display = 'none';
        }
        document.getElementById('mobile-cmd-input').addEventListener('keydown', function(e) {
            if (e.key === 'Enter') { e.preventDefault(); sendMobileInput(); }
        });

        // ── Pane focus tracking ──────────────────────────────────────────────
        document.querySelectorAll('.pane').forEach(function(pane) {
            pane.addEventListener('mousedown', function() {
                document.querySelectorAll('.pane').forEach(p => p.classList.remove('focused'));
                pane.classList.add('focused');
            });
            pane.addEventListener('focus', function() {
                document.querySelectorAll('.pane').forEach(p => p.classList.remove('focused'));
                pane.classList.add('focused');
            });
        });

        // ── Draggable divider (mouse + touch) ───────────────────────────────
        (function() {
            const divider = document.getElementById('divider');
            const container = document.getElementById('split-container');
            const leftPane = document.getElementById('galaxy-pane');
            const rightPane = document.getElementById('telnet-pane');
            let dragging = false;

            function resizeFromPointer(clientX, clientY) {
                const rect = container.getBoundingClientRect();
                if (window.innerWidth <= 768) {
                    // Mobile: divider is horizontal, resize top/bottom heights
                    let topH = ((clientY - rect.top) / rect.height) * 100;
                    topH = Math.max(15, Math.min(85, topH));
                    leftPane.style.height = topH + '%';
                    rightPane.style.height = (100 - topH) + '%';
                } else {
                    let leftW = ((clientX - rect.left) / rect.width) * 100;
                    leftW = Math.max(15, Math.min(85, leftW));
                    leftPane.style.width = leftW + '%';
                    rightPane.style.width = (100 - leftW) + '%';
                }
                if (typeof fitAddon !== 'undefined') fitAddon.fit();
            }

            // Mouse (desktop)
            divider.addEventListener('mousedown', function(e) {
                dragging = true;
                e.preventDefault();
                document.body.style.cursor = 'col-resize';
                document.body.style.userSelect = 'none';
            });
            document.addEventListener('mousemove', function(e) {
                if (!dragging) return;
                resizeFromPointer(e.clientX, e.clientY);
            });
            document.addEventListener('mouseup', function() {
                if (dragging) {
                    dragging = false;
                    document.body.style.cursor = '';
                    document.body.style.userSelect = '';
                    if (typeof fitAddon !== 'undefined') fitAddon.fit();
                }
            });

            // Touch (mobile/tablet)
            divider.addEventListener('touchstart', function(e) {
                dragging = true;
                e.preventDefault();
            }, { passive: false });
            document.addEventListener('touchmove', function(e) {
                if (!dragging) return;
                e.preventDefault();
                var t = e.touches[0];
                resizeFromPointer(t.clientX, t.clientY);
            }, { passive: false });
            document.addEventListener('touchend', function() {
                if (dragging) {
                    dragging = false;
                    if (typeof fitAddon !== 'undefined') fitAddon.fit();
                }
            });
        })();

        // ── xterm.js terminal (24 rows x 80 cols) ───────────────────────────
        const TERM_ROWS = 24;
        const TERM_COLS = 80;

        // Choose terminal font size to match the galaxy chart's responsive breakpoints:
        //   ≤480px → 8px (matches .galaxy-grid @media max-width:480px)
        //   ≤768px → 10px (matches .galaxy-grid @media max-width:768px)
        //   >768px → 12px (matches .galaxy-grid desktop font-size: 12px)
        function chooseFontSize() {
            const w = window.innerWidth;
            if (w <= 480) return 8;
            if (w <= 768) return 10;
            return 12;
        }

        const term = new Terminal({
            cursorBlink: true,
            theme: { background: '#000000', foreground: '#00ff00', cursor: '#00ff00' },
            fontFamily: 'monospace',
            fontSize: chooseFontSize(),
            scrollback: 5000,
            convertEol: false,
        });
        const fitAddon = new FitAddon.FitAddon();
        term.loadAddon(fitAddon);
        term.open(document.getElementById('terminal-container'));

        // Size the terminal to fill the available wrapper space
        function sizeTerminalWrapper() {
            // Let xterm's FitAddon compute the correct cols/rows from the
            // current container size; do NOT set explicit pixel dimensions on
            // the wrapper — that was what caused the bottom to be clipped when
            // the pane was resized to a height smaller than the fixed value.
            fitAddon.fit();
        }
        // After open, fit to declared size
        setTimeout(function() {
            fitAddon.fit();
            sizeTerminalWrapper();
        }, 50);

        window.addEventListener('resize', function() {
            setTimeout(function() {
                // Update font size to match galaxy chart breakpoints before re-fitting
                term.options.fontSize = chooseFontSize();
                fitAddon.fit();
                sizeTerminalWrapper();
            }, 150);
        });

        // ── WebSocket / Telnet connection ────────────────────────────────────
        let ws = null;
        const statusEl = document.getElementById('telnet-status');

        function connectTelnet() {
            if (ws && (ws.readyState === WebSocket.OPEN || ws.readyState === WebSocket.CONNECTING)) {
                ws.close();
            }
            statusEl.textContent = 'Connecting...';
            statusEl.style.color = '#ff0';
            const proto = location.protocol === 'https:' ? 'wss:' : 'ws:';
            ws = new WebSocket(proto + '//' + location.host + '/telnet/ws');
            ws.binaryType = 'arraybuffer';

            ws.onopen = function() {
                statusEl.textContent = 'Connected';
                statusEl.style.color = '#0f0';
            };
            ws.onclose = function() {
                statusEl.textContent = 'Disconnected';
                statusEl.style.color = '#f00';
                term.write('\r\n\x1b[31m--- Connection closed ---\x1b[0m\r\n');
            };
            ws.onerror = function() {
                statusEl.textContent = 'Error';
                statusEl.style.color = '#f00';
            };
            ws.onmessage = function(evt) {
                if (evt.data instanceof ArrayBuffer) {
                    term.write(new Uint8Array(evt.data));
                } else {
                    term.write(evt.data);
                }
            };
        }

        function reconnectTelnet() {
            term.clear();
            connectTelnet();
        }

        // Prevent browser from intercepting Ctrl-B and Ctrl-W; explicitly send ESC.
        term.attachCustomKeyEventHandler(function(e) {
            if (e.type === 'keydown') {
                // Explicitly capture and send the Escape key so browsers that
                // suppress it (or xterm versions that do not emit it via onData)
                // still forward ASCII 27 to the game server.
                if (e.key === 'Escape' && !e.ctrlKey && !e.altKey && !e.metaKey) {
                    if (ws && ws.readyState === WebSocket.OPEN) {
                        ws.send('\x1b');
                    }
                    e.preventDefault();
                    return false; // tell xterm we handled it; suppress onData duplicate
                }
            }
            if (e.ctrlKey && !e.altKey && !e.metaKey) {
                var key = e.key.toLowerCase();
                if (key === 'b' || key === 'w') {
                    e.preventDefault();
                    return true;
                }
            }
            return true;
        });

        term.onData(function(data) {
            if (ws && ws.readyState === WebSocket.OPEN) {
                ws.send(data);
            }
        });

        // Focus telnet pane when terminal is clicked
        document.getElementById('terminal-container').addEventListener('mousedown', function() {
            document.querySelectorAll('.pane').forEach(p => p.classList.remove('focused'));
            document.getElementById('telnet-pane').classList.add('focused');
            term.focus();
        });

        // Start connection
        connectTelnet();

        // ── Galaxy chart ─────────────────────────────────────────────────────
        let currentGalaxy = 0;
        let galaxyObjects = {};

        // Mobile detection
        const isMobile = /Android|webOS|iPhone|iPad|iPod|BlackBerry|IEMobile|Opera Mini/i.test(navigator.userAgent)
            || ('ontouchstart' in window)
            || (window.innerWidth <= 768);

        // Compute character metrics based on current grid font
        function getCharMetrics() {
            const grid = document.getElementById('galaxy-grid');
            const style = window.getComputedStyle(grid);
            const fontSize = parseFloat(style.fontSize);
            const lineHeight = parseFloat(style.lineHeight);
            // Monospace char width is roughly 0.6 * fontSize
            const charWidth = fontSize * 0.6;
            return { charWidth: charWidth, lineHeight: lineHeight };
        }

        function formatObjectPopup(obj) {
            // Helper to format missing or undefined fields
            function val(v, def) {
                return (v !== undefined && v !== null) ? v : def;
            }

            // Shields formatting
            const initialShieldValue = 25000; // From Go constants
            let shieldPct = val(obj.shields, 0) / initialShieldValue * 100.0;
            let shieldudflag = obj.shieldsUpDown ? '+' : '-';
            let shieldStr = shieldudflag + shieldPct.toFixed(0) + '%';
            let shieldsValue = shieldStr + ' ' + (val(obj.shields, 0) / 10).toFixed(1);

            // Compose the popup content
            let popup =
                'Stardate        ' + val(obj.starDate, 0) + '\n' +
                'Condition       ' + val(obj.condition, 'Green') + '\n' +
                'Location        ' + val(obj.locationX, 0) + '-' + val(obj.locationY, 0) + '\n' +
                'Torpedoes       ' + val(obj.torpedoTubes, 0) + '\n' +
                'Energy          ' + (val(obj.shipEnergy, 0) / 10).toFixed(1) + '\n' +
                'Damage          ' + (val(obj.totalShipDamage, 0) / 100).toFixed(1) + '\n' +
                'Shields         ' + shieldsValue + ' units\n' +
                'Radio           ' + (obj.radioOnOff ? 'On' : 'Off') + '\n';

            // Append the damage report at the bottom, if present
            if (obj.damageReport) {
                popup += '\n' + obj.damageReport;
            }
            return popup;
        }

        function formatPopupHeading(obj) {
            var side = (obj.side || '').toLowerCase();
            var type = obj.type || '';
            var sideName = '';
            if (side === 'federation') {
                sideName = 'Federation';
            } else if (side === 'empire') {
                sideName = 'Empire';
            } else if (side === 'romulan') {
                sideName = 'Romulan';
            } else if (side === 'neutral') {
                sideName = 'Neutral';
            }
            // For Stars and Black Holes, side is not meaningful
            if (type === 'Star' || type === 'Black Hole') {
                return type;
            }
            var heading = sideName ? sideName + ' ' + type : type;
            if (obj.name && obj.name !== obj.type) {
                heading += ' - ' + obj.name;
            }
            return heading;
        }

        function showObjectPopup(x, y, obj) {
            const popup = document.getElementById('object-popup');
            popup.innerHTML = '<div class="header">' + formatPopupHeading(obj) + '</div>' +
                            formatObjectPopup(obj);
            popup.style.display = 'block';

            if (isMobile) {
                // On mobile, popup is fixed at bottom via CSS; no manual positioning needed
                popup.style.left = '';
                popup.style.top = '';
                return;
            }

            // Desktop: position popup to the right of cursor, check screen bounds
            let leftPos = x + 15;
            let topPos = y - 10;

            // Adjust if popup would go off screen
            if (leftPos + 300 > window.innerWidth) {
                leftPos = x - 320; // Show to the left instead
            }
            if (topPos < 0) {
                topPos = y + 20; // Show below cursor instead
            }

            popup.style.left = leftPos + 'px';
            popup.style.top = topPos + 'px';
        }

        function hideObjectPopup() {
            document.getElementById('object-popup').style.display = 'none';
        }

        function addHoverListeners(data) {
            const grid = document.getElementById('galaxy-grid');

            // Clear existing overlays
            const existingOverlays = grid.querySelectorAll('.hover-overlay');
            existingOverlays.forEach(overlay => overlay.remove());

            // Get galaxy dimensions from the data
            const maxSizeX = data.maxSizeX || 75;
            const maxSizeY = data.maxSizeY || 75;

            // Get current character metrics (responsive to font-size changes)
            const metrics = getCharMetrics();
            const charWidth = metrics.charWidth;
            const lineHeight = metrics.lineHeight;

            // Create overlays directly from object coordinates
            Object.entries(galaxyObjects).forEach(([objKey, obj]) => {
                const [row, col] = objKey.split(',').map(Number);

                // Calculate grid position using the scan format dynamically
                const lineIndex = (maxSizeX + 1) - row;

                // Calculate column position in characters
                const rowNumWidth = row < 10 ? 2 : 3;
                const charPosition = rowNumWidth + col - 1;

                // Apply offset correction: +2 vertical (down), +2 horizontal (right)
                const correctedLeft = (charPosition + 2) * charWidth;
                const correctedTop = ((lineIndex - 1) + 2) * lineHeight;

                // Create overlay - larger on mobile for easier tapping
                const overlay = document.createElement('span');
                overlay.className = 'hover-overlay';
                overlay.style.position = 'absolute';
                overlay.style.left = correctedLeft + 'px';
                overlay.style.top = correctedTop + 'px';
                overlay.style.cursor = 'pointer';
                overlay.style.zIndex = '10';
                overlay.style.pointerEvents = 'auto';

                if (isMobile) {
                    // Larger touch targets on mobile (minimum 24px)
                    const touchSize = Math.max(charWidth, 24);
                    const touchHeight = Math.max(lineHeight, 24);
                    overlay.style.width = touchSize + 'px';
                    overlay.style.height = touchHeight + 'px';
                    // Center the enlarged touch target on the character
                    overlay.style.marginLeft = -((touchSize - charWidth) / 2) + 'px';
                    overlay.style.marginTop = -((touchHeight - lineHeight) / 2) + 'px';

                    overlay.addEventListener('touchstart', function(e) {
                        e.preventDefault();
                        e.stopPropagation();
                        const touch = e.touches[0];
                        showObjectPopup(touch.pageX, touch.pageY, obj);
                    }, { passive: false });
                } else {
                    overlay.style.width = charWidth + 'px';
                    overlay.style.height = lineHeight + 'px';

                    overlay.addEventListener('mouseenter', function(e) {
                        showObjectPopup(e.pageX, e.pageY, obj);
                    });
                    overlay.addEventListener('mouseleave', hideObjectPopup);
                }

                grid.appendChild(overlay);
            });
        }

        // Dismiss popup when tapping outside on mobile
        if (isMobile) {
            document.addEventListener('touchstart', function(e) {
                if (!e.target.closest('.hover-overlay') && !e.target.closest('.object-popup')) {
                    hideObjectPopup();
                }
            });
            // Tap the popup itself to dismiss it (no mouseleave on mobile)
            document.getElementById('object-popup').addEventListener('touchstart', function(e) {
                hideObjectPopup();
                e.stopPropagation();
            });
        }

        function updateGalaxyDisplay(data) {
            const grid = document.getElementById('galaxy-grid');

            // Clear existing overlays
            const overlays = grid.querySelectorAll('span');
            overlays.forEach(overlay => overlay.remove());

            // Convert \r\n to \n and escape HTML
            const scanOutput = data.scanOutput.replace(/\r\n/g, '\n').replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
            grid.textContent = scanOutput;

            // Store object data
            galaxyObjects = data.objects;

            // Add hover listeners for objects
            setTimeout(() => addHoverListeners(data), 100);
        }

        function refreshData() {
            const galaxy = document.getElementById('galaxy-select').value;
            document.getElementById('status').textContent = 'Refreshing...';

            fetch('/galaxy/' + galaxy + '/data')
                .then(response => response.json())
                .then(data => {
                    updateGalaxyDisplay(data);
                    document.getElementById('status').textContent = 'Last updated: ' + new Date().toLocaleTimeString();
                })
                .catch(error => {
                    document.getElementById('status').textContent = 'Error: ' + error.message;
                });
        }

        // Auto-refresh every 5 seconds
        setInterval(refreshData, 5000);

        // Initial load
        refreshData();

        // Handle galaxy selection change
        document.getElementById('galaxy-select').addEventListener('change', refreshData);
    </script>
</body>
</html>
`

	tmpl := template.Must(template.New("index").Parse(htmlTemplate))

	httpRL := NewHTTPRateLimiter()

	// Root handler
	http.Handle("/", httpRL.Middleware(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		data := struct {
			Galaxies []int
		}{
			Galaxies: make([]int, MaxGalaxies),
		}
		for i := 0; i < MaxGalaxies; i++ {
			data.Galaxies[i] = i
		}
		tmpl.Execute(w, data)
	})))

	// Galaxy data endpoint
	http.Handle("/galaxy/", httpRL.Middleware(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		// Parse galaxy ID from URL
		path := strings.TrimPrefix(r.URL.Path, "/galaxy/")
		parts := strings.Split(path, "/")
		if len(parts) != 2 || parts[1] != "data" {
			http.NotFound(w, r)
			return
		}

		galaxyID, err := strconv.ParseUint(parts[0], 10, 16)
		if err != nil || galaxyID >= MaxGalaxies {
			http.Error(w, "Invalid galaxy ID", http.StatusBadRequest)
			return
		}

		data := i.getGalaxyData(uint16(galaxyID), true)

		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(data)
	})))

	// WebSocket handler for the telnet pane embedded in the god-mode page.
	// The god-mode page is served on port WebServerPort (1702) and its JavaScript
	// connects to /telnet/ws on the *same* host:port the page was loaded from.
	// Without this handler, port 1702 has no /telnet/ws route and the WebSocket
	// upgrade returns 404, which is why the terminal shows "Disconnected" /
	// "--- Connection closed ---" immediately on load or reconnect.
	godModeWsUpgrader := websocket.Upgrader{
		CheckOrigin: func(r *http.Request) bool { return true },
	}
	http.Handle("/telnet/ws", httpRL.Middleware(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		wsConn, err := godModeWsUpgrader.Upgrade(w, r, nil)
		if err != nil {
			log.Printf("God-mode telnet WebSocket upgrade error: %v", err)
			return
		}
		defer wsConn.Close()

		tcpConn, err := net.DialTimeout("tcp", fmt.Sprintf("127.0.0.1:%d", ServerPort), 10*time.Second)
		if err != nil {
			log.Printf("God-mode telnet TCP connect error: %v", err)
			wsConn.WriteMessage(websocket.TextMessage, []byte("Failed to connect to game server.\r\n"))
			return
		}
		defer tcpConn.Close()

		done := make(chan struct{})

		// TCP -> WebSocket
		go func() {
			defer close(done)
			buf := make([]byte, 4096)
			for {
				n, readErr := tcpConn.Read(buf)
				if n > 0 {
					if writeErr := wsConn.WriteMessage(websocket.BinaryMessage, buf[:n]); writeErr != nil {
						return
					}
				}
				if readErr != nil {
					if readErr != io.EOF {
						log.Printf("God-mode telnet TCP read error: %v", readErr)
					}
					return
				}
			}
		}()

		// WebSocket -> TCP
		go func() {
			for {
				_, msg, readErr := wsConn.ReadMessage()
				if readErr != nil {
					tcpConn.Close()
					return
				}
				if _, writeErr := tcpConn.Write(msg); writeErr != nil {
					return
				}
			}
		}()

		<-done
	})))

	fmt.Printf("Web server starting on :%d\n", WebServerPort)
	go func() {
		if err := http.ListenAndServe(fmt.Sprintf(":%d", WebServerPort), nil); err != nil {
			fmt.Printf("Web server error: %v\n", err)
		}
	}()
}

func (i *Interpreter) startTelnetWebServer() {
	mux := http.NewServeMux()

	// Port 1703 is served behind the reverse proxy; real client IPs arrive via
	// X-Forwarded-For / X-Real-IP.
	httpRL := NewHTTPRateLimiter()

	var upgrader = websocket.Upgrader{
		CheckOrigin: func(r *http.Request) bool { return true },
	}

	telnetHTML := `<!DOCTYPE html>
<html>
<head>
<meta name="viewport" content="width=device-width, initial-scale=1.0, maximum-scale=1.0, user-scalable=no">
<title>GoWars Telnet Client</title>
<style>
  #refresh-btn {
    font-size: 12px;
    padding: 2px 10px;
    background: #222;
    color: #0f0;
    border: 1px solid #0f0;
    cursor: pointer;
  }
  #refresh-btn:hover {
    background: #0f0;
    color: #000;
  }
</style>
<link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/xterm@5.3.0/css/xterm.css" />
<script src="https://cdn.jsdelivr.net/npm/xterm@5.3.0/lib/xterm.js"></script>
<script src="https://cdn.jsdelivr.net/npm/xterm-addon-fit@0.8.0/lib/xterm-addon-fit.js"></script>
<style>
  * { box-sizing: border-box; }
  html, body { height: 100%; margin: 0; padding: 0; overflow: hidden; background: #000; color: #0f0; font-family: monospace; }
  body { display: flex; flex-direction: column; }

  /* ── Header ── */
  #header {
    display: flex; align-items: center; gap: 8px;
    padding: 3px 8px; background: #0a0a0a;
    border-bottom: 1px solid #1a1a1a; flex-shrink: 0;
  }
  #header h1 { color: #0f0; margin: 0; font-size: 14px; flex: 1; }
  #status { color: #ff0; font-size: 11px; }

  /* ── Terminal area ── */
  /* On desktop: fill remaining height. On mobile: overridden below. */
  #terminal-container { flex: 1; min-height: 0; width: 100%; }

  /* ── Mobile button panel (hidden on desktop) ── */
  #mobile-panel {
    display: none;
    flex-shrink: 0;
    flex-direction: column;
    background: #0d0d0d;
    border-top: 1px solid #333;
    padding: 3px 4px;
    gap: 2px;
    flex: 0 0 auto;
    /* Panel height is driven by its content; no max-height cap on mobile */
  }

  /* Top: numeric pad — single row of digits */
  #numpad {
    display: grid;
    grid-template-columns: repeat(10, 1fr);
    gap: 2px;
    flex-shrink: 0;
  }

  /* Bottom: context-aware command buttons — NO scroll, wraps naturally */
  #action-buttons {
    display: grid;
    grid-template-columns: repeat(8, 1fr);
    gap: 2px;
    align-content: start;
    overflow: hidden;
  }
  /* Each .action-row is now just a CSS subgrid row of buttons;
     we override display so buttons flow directly into the parent grid */
  .action-row {
    display: contents;
  }
  .yellow-row {
    /* no extra margin needed — gap handles spacing */
  }
  #enter-row {
    display: grid;
    grid-template-columns: repeat(4, 1fr);
    gap: 2px;
    flex-shrink: 0;
  }

  /* Shared button styles */
  .act-btn, .num-btn {
    background: #111;
    color: #0f0;
    border: 1px solid #0f0;
    border-radius: 3px;
    font-family: monospace;
    font-weight: bold;
    font-size: 9px;
    cursor: pointer;
    user-select: none;
    -webkit-user-select: none;
    touch-action: manipulation;
    display: flex; align-items: center; justify-content: center;
    min-height: 22px;
    padding: 1px 0;
    transition: background 0.08s, color 0.08s;
  }
  .act-btn:active, .num-btn:active { background: #0f0; color: #000; }

  /* Yellow button style for specific buttons */
  .yellow-btn {
    background: #222 !important;
    color: #ff0 !important;
    border: 1px solid #ff0 !important;
  }

  /* ── Mobile: show panel; terminal height driven entirely by JS ── */
  @media (max-width: 768px) {
    body { padding: 0; }
    #mobile-panel { display: flex; }
    /* Minimal CSS fallback only – JS will replace this with exact px value
       derived from measuring the panel after buttons are rendered. */
    #terminal-container { flex: none; height: 30vh; }
  }

  /* Desktop keeps a light padding */
  @media (min-width: 769px) {
    body { padding: 10px; }
    #header h1 { font-size: 18px; }
    #status { font-size: 13px; }
  }
</style>
</head>
<body>
<div id="header">
  <h1>GoWars Telnet</h1>
  <span id="status">Connecting...</span>
  <button id="refresh-btn" onclick="refreshTelnet()">Refresh</button>
</div>
<div id="terminal-container"></div>

<!-- Mobile control panel: shown only on small screens -->
<div id="mobile-panel">
  <!-- Top: numeric pad (row 1: digits, row 2: Enter) -->
  <div id="numpad">
    <button class="num-btn" onclick="sendRaw('1')">1</button>
    <button class="num-btn" onclick="sendRaw('2')">2</button>
    <button class="num-btn" onclick="sendRaw('3')">3</button>
    <button class="num-btn" onclick="sendRaw('4')">4</button>
    <button class="num-btn" onclick="sendRaw('5')">5</button>
    <button class="num-btn" onclick="sendRaw('6')">6</button>
    <button class="num-btn" onclick="sendRaw('7')">7</button>
    <button class="num-btn" onclick="sendRaw('8')">8</button>
    <button class="num-btn" onclick="sendRaw('9')">9</button>
    <button class="num-btn" onclick="sendRaw('0')">0</button>
  </div>

  <!-- Bottom: context-aware command buttons -->
  <div id="action-buttons">
    <!-- populated by updateActionButtons() -->
  </div>
  <div id="enter-row">
    <button class="num-btn yellow-btn" onclick="sendRaw('\x1b')">&#9099; Esc</button>
    <button class="num-btn yellow-btn" onclick="sendRaw('\x03')">&#8984; ^C</button>
    <button class="num-btn yellow-btn" onclick="triggerSpacebar()">Space</button>
    <button class="num-btn yellow-btn" onclick="sendRaw('\r')">&#9166; Enter</button>
  </div>
</div>

<script>
  // Mobile detection
  const isMobile = /Android|webOS|iPhone|iPad|iPod|BlackBerry|IEMobile|Opera Mini/i.test(navigator.userAgent)
      || ('ontouchstart' in window)
      || (window.innerWidth <= 768);

  // Choose font size based on device type and screen width
  function chooseFontSize() {
    if (!isMobile) return 14;
    const w = window.innerWidth;
    if (w <= 360) return 10;
    if (w <= 480) return 11;
    return 12;
  }

  // ── sizeTerminal ─────────────────────────────────────────────────────────
  // On mobile: measure the panel's actual rendered height and set the terminal
  // container to exactly the remaining space.  Must be called:
  //   • after buttons are injected (panel grows),
  //   • after term.open (initial fit),
  //   • on every viewport / visualViewport resize.
  // On desktop the terminal keeps flex:1 and this is a no-op height-wise.
  const fitAddon = new FitAddon.FitAddon();
  function sizeTerminal() {
    if (isMobile) {
      const vph = window.visualViewport ? window.visualViewport.height : window.innerHeight;
      const headerH = document.getElementById('header').offsetHeight;
      const panelH  = document.getElementById('mobile-panel').offsetHeight;
      const avail   = vph - headerH - panelH;
      document.getElementById('terminal-container').style.height = Math.max(avail, 60) + 'px';
    }
    fitAddon.fit();
  }

  // Command lists keyed by prompt
  const PG_CMDS = [
    'ACtivate','GRipe','HElp','NEws','QUit','SEt','SUmmary','TEll','TIme','USers'
  ];
  const GAME_CMDS = [
    'ADmin','BAses','BUild','CApture','DAmages','DOck','ENergy','GRipe','HElp',
    'IMpulse','LIst','MOve','NEws','PHasers','PLanets','POints','QUit','RAdio','REpair',
    'SCan','SEt','SHields','SRscan','STatus','SUmmary','TArgets','TEll','TIme',
    'TOrpedoes','TRactor','TYpe','USers'
  ];

  let currentPrompt = 'PG>';  // default until we hear from server

  function updateActionButtons(prompt) {
    const container = document.getElementById('action-buttons');
    const cmds = (prompt === 'Command:') ? GAME_CMDS : PG_CMDS;
    // Render command buttons flat — they flow into the 8-column CSS grid directly
    let html = cmds.map(c =>
      '<button class="act-btn" onclick="insertCmd(\'' + c + '\')">' + c + '</button>'
    ).join('');
    // Yellow sub-command buttons
    const specialCmds = ['neutral', 'enemy', 'friendly', 'ships', 'bases', 'planets'];
    html += specialCmds.map(c =>
      '<button class="act-btn yellow-btn" onclick="insertCmd(\'' + c + '\')">' + c + '</button>'
    ).join('');
    // In game mode add nav buttons (/, ?, -)
    if (prompt === 'Command:') {
      html += '<button class="act-btn yellow-btn" onclick="insertCmd(\'/\')">/</button>' +
              '<button class="act-btn yellow-btn" onclick="insertCmd(\'?\')">?</button>' +
              '<button class="act-btn yellow-btn" style="grid-column:span 2;" onclick="insertCmd(\'-\')">-</button>';
    }
    container.innerHTML = html;
    // Panel height just changed — resize terminal immediately.
    sizeTerminal();
  }

  // Detect prompt in incoming data (scan last 32 bytes of each message)
  function detectPrompt(text) {
    if (text.indexOf('Command: ') !== -1 || text.endsWith('Command: ')) {
      return 'Command:';
    }
    if (text.indexOf('PG> ') !== -1 || text.endsWith('PG> ')) {
      return 'PG>';
    }
    return null;
  }

  // ── CRITICAL INIT ORDER ──────────────────────────────────────────────────
  // Step 1: inject buttons into DOM so the panel has its full height BEFORE
  //         we open xterm and measure available space.
  updateActionButtons(currentPrompt);

  // Step 2: open xterm into the container (which already has the CSS 30vh
  //         fallback height, but panel is now fully rendered for measurement).
  const term = new Terminal({
    cursorBlink: true,
    theme: { background: '#000000', foreground: '#00ff00', cursor: '#00ff00' },
    fontFamily: 'monospace',
    fontSize: chooseFontSize(),
    scrollback: 5000,
    convertEol: false,
  });
  term.loadAddon(fitAddon);
  term.open(document.getElementById('terminal-container'));

  // Step 3: set the exact pixel height and fit cols/rows.
  sizeTerminal();

  // Debounced resize + virtualViewport handler
  let resizeTimer = null;
  function debouncedSize() {
    if (resizeTimer) clearTimeout(resizeTimer);
    resizeTimer = setTimeout(sizeTerminal, 150);
  }
  window.addEventListener('resize', debouncedSize);
  if (window.visualViewport) {
    window.visualViewport.addEventListener('resize', debouncedSize);
  }

  const statusEl = document.getElementById('status');
  const proto = location.protocol === 'https:' ? 'wss:' : 'ws:';
  // Build WebSocket URL correctly whether served directly on :1703 or via reverse proxy at /telnet.
  const rawPath = location.pathname.replace(/\/$/, '');
  const basePath = rawPath.replace(/\/telnet$/, '');
  const ws = new WebSocket(proto + '//' + location.host + basePath + '/ws');
  ws.binaryType = 'arraybuffer';

  ws.onopen = function() { statusEl.textContent = 'Connected'; statusEl.style.color = '#0f0'; };
  ws.onclose = function() { statusEl.textContent = 'Disconnected'; statusEl.style.color = '#f00'; term.write('\r\n\x1b[31m--- Connection closed ---\x1b[0m\r\n'); };
  ws.onerror = function() { statusEl.textContent = 'Error'; statusEl.style.color = '#f00'; };

  ws.onmessage = function(evt) {
    let data;
    if (evt.data instanceof ArrayBuffer) {
      data = new Uint8Array(evt.data);
      term.write(data);
      // decode for prompt detection
      try {
        const text = new TextDecoder().decode(data);
        const p = detectPrompt(text);
        if (p && p !== currentPrompt) { currentPrompt = p; updateActionButtons(p); }
      } catch(e) {}
    } else {
      term.write(evt.data);
      const p = detectPrompt(evt.data);
      if (p && p !== currentPrompt) { currentPrompt = p; updateActionButtons(p); }
    }
  };

  // Prevent browser from intercepting Ctrl-B and Ctrl-W; explicitly send ESC.
  term.attachCustomKeyEventHandler(function(e) {
    if (e.type === 'keydown') {
      // Explicitly capture and send the Escape key so browsers that
      // suppress it (or xterm versions that do not emit it via onData)
      // still forward ASCII 27 to the game server.
      if (e.key === 'Escape' && !e.ctrlKey && !e.altKey && !e.metaKey) {
        if (ws && ws.readyState === WebSocket.OPEN) {
          ws.send('\x1b');
        }
        e.preventDefault();
        return false; // tell xterm we handled it; suppress onData duplicate
      }
    }
    if (e.ctrlKey && !e.altKey && !e.metaKey) {
      var key = e.key.toLowerCase();
      if (key === 'b' || key === 'w') {
        e.preventDefault();
        return true;
      }
    }
    return true;
  });

  // Handle terminal input (keyboard and mobile)
  term.onData(function(data) {
    for (let i = 0; i < data.length; ++i) {
      let ch = data[i];
      if (ws.readyState === WebSocket.OPEN) {
        ws.send(ch); // Send each character directly to the server
      }
    }
  });

  // insertCmd: send a command name over the WebSocket; server echo handles display
  function insertCmd(name) {
    if (ws && ws.readyState === WebSocket.OPEN) {
      for (var i = 0; i < name.length; i++) {
        ws.send(name[i]);
      }
    }
  }

  // triggerSpacebar: send a space over the WebSocket; server echo handles display
  function triggerSpacebar() {
    if (ws && ws.readyState === WebSocket.OPEN) {
      ws.send(' ');
    }
  }

  // sendRaw: send raw character(s) directly; server echo handles display
  function sendRaw(ch) {
    if (ws && ws.readyState === WebSocket.OPEN) {
      ws.send(ch);
    } else {
      console.error("WebSocket is not open. Unable to send:", ch);
    }
  }

  // On mobile, focus terminal on tap so virtual keyboard can open
  if (isMobile) {
    document.getElementById('terminal-container').addEventListener('touchstart', function() {
      term.focus();
    });
  }
function refreshTelnet() {
  if (ws && ws.readyState === WebSocket.OPEN) {
    ws.close();
  }
  statusEl.textContent = 'Refreshing...';
  statusEl.style.color = '#ff0';
  setTimeout(() => {
    term.clear();
    location.reload();
  }, 500);
}
</script>
</body>
</html>`

	mux.Handle("/", httpRL.Middleware(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Content-Type", "text/html; charset=utf-8")
		w.Write([]byte(telnetHTML))
	})))

	mux.Handle("/ws", httpRL.Middleware(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		wsConn, err := upgrader.Upgrade(w, r, nil)
		if err != nil {
			log.Printf("Telnet WebSocket upgrade error: %v", err)
			return
		}
		defer wsConn.Close()

		// Connect to the telnet server on localhost:1701
		tcpConn, err := net.DialTimeout("tcp", fmt.Sprintf("127.0.0.1:%d", ServerPort), 10*time.Second)
		if err != nil {
			log.Printf("Telnet TCP connect error: %v", err)
			wsConn.WriteMessage(websocket.TextMessage, []byte("Failed to connect to game server.\r\n"))
			return
		}
		defer tcpConn.Close()

		done := make(chan struct{})

		// TCP -> WebSocket
		go func() {
			defer func() { close(done) }()
			buf := make([]byte, 4096)
			for {
				n, err := tcpConn.Read(buf)
				if n > 0 {
					if writeErr := wsConn.WriteMessage(websocket.BinaryMessage, buf[:n]); writeErr != nil {
						return
					}
				}
				if err != nil {
					if err != io.EOF {
						log.Printf("Telnet TCP read error: %v", err)
					}
					return
				}
			}
		}()

		// WebSocket -> TCP
		go func() {
			for {
				_, msg, err := wsConn.ReadMessage()
				if err != nil {
					tcpConn.Close()
					return
				}
				if _, err := tcpConn.Write(msg); err != nil {
					return
				}
			}
		}()

		<-done
	})))

	fmt.Printf("Telnet web client starting on :%d\n", TelnetWebPort)
	go func() {
		if err := http.ListenAndServe(fmt.Sprintf(":%d", TelnetWebPort), mux); err != nil {
			fmt.Printf("Telnet web server error: %v\n", err)
		}
	}()
}

// proxyWebSocket tunnels a WebSocket upgrade request to a backend address.
// httputil.NewSingleHostReverseProxy does not support WebSocket upgrades, so
// we implement a raw TCP tunnel for any request that carries "Upgrade: websocket".
func proxyWebSocket(w http.ResponseWriter, r *http.Request, backendAddr string) {
	backendConn, err := net.DialTimeout("tcp", backendAddr, 10*time.Second)
	if err != nil {
		http.Error(w, "Backend unavailable", http.StatusBadGateway)
		return
	}
	defer backendConn.Close()

	// Hijack the client connection so we can speak raw TCP.
	hijacker, ok := w.(http.Hijacker)
	if !ok {
		http.Error(w, "Hijacking not supported", http.StatusInternalServerError)
		return
	}
	clientConn, buf, err := hijacker.Hijack()
	if err != nil {
		http.Error(w, "Hijack failed", http.StatusInternalServerError)
		return
	}
	defer clientConn.Close()

	// Flush anything already buffered to the backend.
	if buf.Reader.Buffered() > 0 {
		buffered, _ := buf.Reader.Peek(buf.Reader.Buffered())
		backendConn.Write(buffered)
	}

	// Re-write the original HTTP upgrade request to the backend.
	r.Write(backendConn)

	// Bidirectional copy.
	done := make(chan struct{}, 2)
	cp := func(dst net.Conn, src net.Conn) {
		io.Copy(dst, src)
		done <- struct{}{}
	}
	go cp(backendConn, clientConn)
	go cp(clientConn, backendConn)
	<-done
}

func (i *Interpreter) startReverseProxy() {
	godModeURL, _ := url.Parse(fmt.Sprintf("http://127.0.0.1:%d", WebServerPort))
	telnetBackendAddr := fmt.Sprintf("127.0.0.1:%d", TelnetWebPort)

	godModeProxy := httputil.NewSingleHostReverseProxy(godModeURL)
	// Ensure the god-mode proxy sets the correct Host header for the backend.
	godModeProxy.Director = func(req *http.Request) {
		req.URL.Scheme = "http"
		req.URL.Host = fmt.Sprintf("127.0.0.1:%d", WebServerPort)
		req.Host = fmt.Sprintf("127.0.0.1:%d", WebServerPort)
	}

	mux := http.NewServeMux()

	// /telnet/* -> strip prefix, proxy to telnet web client on port 1703.
	// WebSocket upgrades (e.g. /telnet/ws) are tunnelled via raw TCP because
	// httputil.NewSingleHostReverseProxy does not support the Upgrade handshake.
	proxyTelnet := func(w http.ResponseWriter, r *http.Request) {
		// Strip the /telnet prefix so the backend sees /ws, /, etc.
		r.URL.Path = strings.TrimPrefix(r.URL.Path, "/telnet")
		if r.URL.Path == "" {
			r.URL.Path = "/"
		}

		if strings.EqualFold(r.Header.Get("Upgrade"), "websocket") {
			// Restore the path in the raw request before tunnelling.
			r.RequestURI = r.URL.RequestURI()
			proxyWebSocket(w, r, telnetBackendAddr)
			return
		}

		// Plain HTTP — use the standard reverse proxy.
		telnetProxy := httputil.NewSingleHostReverseProxy(&url.URL{
			Scheme: "http",
			Host:   telnetBackendAddr,
		})
		telnetProxy.Director = func(req *http.Request) {
			req.URL.Scheme = "http"
			req.URL.Host = telnetBackendAddr
			req.Host = telnetBackendAddr
		}
		telnetProxy.ServeHTTP(w, r)
	}

	mux.HandleFunc("/telnet/", proxyTelnet)
	mux.HandleFunc("/telnet", proxyTelnet)

	// Everything else -> God mode Web UI on port 1702.
	mux.HandleFunc("/", func(w http.ResponseWriter, r *http.Request) {
		godModeProxy.ServeHTTP(w, r)
	})

	fmt.Printf("Reverse proxy starting on :%d (/ -> :%d, /telnet -> :%d)\n",
		ReverseProxyPort, WebServerPort, TelnetWebPort)
	go func() {
		if err := http.ListenAndServe(fmt.Sprintf(":%d", ReverseProxyPort), mux); err != nil {
			fmt.Printf("Reverse proxy error: %v\n", err)
		}
	}()
}

func main() {
	//Start pprof
	go func() {
		http.ListenAndServe("127.0.0.1:6060", nil)
	}()
	os.Create("pprof")
	//End pprof

	listener, err := net.Listen("tcp", fmt.Sprintf(":%d", ServerPort))
	if err != nil {
		panic(fmt.Sprintf("Failed to start server: %v", err))
	}
	defer listener.Close()

	//Initial message
	fmt.Printf("Gowars Server started on :%d\n", ServerPort)

	var connections sync.Map
	interpreter := NewInterpreter(time.Now(), &connections)

	// Start the web server
	interpreter.startWebServer()

	// Start the telnet web client server
	interpreter.startTelnetWebServer()

	// Start the reverse proxy (single port for firewall friendliness)
	interpreter.startReverseProxy()

	// Start the state engine for atomic game state management
	go interpreter.StartStateEngine()

	// Start the cleanup routine
	interpreter.startCleanupRoutine()

	// Handle shutdown gracefully
	sigChan := make(chan os.Signal, 1)
	signal.Notify(sigChan, os.Interrupt, syscall.SIGTERM)

	ipTracker := NewIPTracker()
	go func() {
		<-sigChan
		fmt.Println("\nShutting down server...")
		interpreter.Shutdown()
		listener.Close()
		os.Exit(0)
	}()

	for {
		conn, err := listener.Accept()
		if err != nil {
			continue
		}

		// Check connection limit based on DecwarMode
		currentConnections := interpreter.countConnections()
		var maxConnections int
		if DecwarMode {
			maxConnections = DecwarModeMaxUsers
		} else {
			maxConnections = goWarsModeMaxUsers
		}

		if currentConnections >= maxConnections {
			// Send rejection message and close connection
			conn.Write([]byte("Connection limit exceeded. Please try again later.\r\n"))
			conn.Close()
			continue
		}

		ip, _, _ := net.SplitHostPort(conn.RemoteAddr().String())
		if !ipTracker.Allow(ip) {
			conn.Write([]byte("Too many connections from your address.\r\n"))
			conn.Close()
			continue
		}

		go func(c net.Conn, clientIP string) {
			defer ipTracker.Release(clientIP)
			interpreter.handleConnection(c)
		}(conn, ip)
	}
}

// moveTractoredShipIfNeededNoLock moves the tractored ship to a Manhattan cell 1 back from the ending
// location of the player's ship,
// along the path the player's ship just moved. If the path is only 1 cell, the tractored ship ends up in the
// cell the player's ship started from.
// This function must be called with objectsMutex already locked!

func (i *Interpreter) moveTractoredShipIfNeededNoLock(myShip *Object, startX, startY, targetX, targetY int, pathCells [][2]int) {
	if myShip == nil || !myShip.TractorOnOff || myShip.TractorShip == "" {
		return
	}

	galaxy := myShip.Galaxy

	// Find the tractored object (could be a ship, star, planet, etc.)
	var tractoredShip *Object
	for idx := range i.objects {
		obj := i.objects[idx]
		if obj.Name == myShip.TractorShip && obj.Galaxy == galaxy {
			tractoredShip = obj
			break
		}
	}
	if tractoredShip == nil {
		return
	}

	// Determine the cell 1 back from the ending location along the path
	// If pathCells has only 1 cell, use the starting cell
	var destCell [2]int
	if len(pathCells) > 1 {
		destCell = pathCells[len(pathCells)-2]
	} else if len(pathCells) == 1 {
		destCell = [2]int{startX, startY}
	} else {
		destCell = [2]int{startX, startY}
	}

	// Check if the destination cell is occupied by something other than the tractored object itself
	for _, obj := range i.objects {
		if obj.Galaxy == galaxy && obj.Name != tractoredShip.Name &&
			obj.LocationX == destCell[0] && obj.LocationY == destCell[1] {
			// Cell is occupied, do not move tractored object
			return
		}
	}

	// Move the tractored ship
	i.updateObjectLocation(tractoredShip, destCell[0], destCell[1])
	tractoredShip.Condition = "Green"
}

// tractorOff is a helper function that revises the tractor for both ships.
func (i *Interpreter) tractorOff(conn net.Conn) string {
	if info, ok := i.connections.Load(conn); ok {
		connInfo := info.(ConnectionInfo)
		if connInfo.Shipname != "" {
			for idx := range i.objects {
				obj := i.objects[idx]
				if obj.Type == "Ship" && obj.Name == connInfo.Shipname && obj.Galaxy == connInfo.Galaxy {
					// Check if tractor beam is active
					if !obj.TractorOnOff || obj.TractorShip == "" {
						return ("Tractor beam not in operation at this time, Captain.")
					}

					// Find and clear the other ship's tractor state
					for j := range i.objects {
						other := i.objects[j]
						if other.Name == obj.TractorShip && other.Galaxy == obj.Galaxy {
							other.TractorOnOff = false
							other.TractorShip = ""
							// Notify the other ship that the tractor beam is broken
							i.notifyShipTractorBroken(other.Name, other.Galaxy)
							break
						}
					}

					// Clear this ship's tractor state
					obj.TractorOnOff = false
					obj.TractorShip = ""
					break
				}
			}
		}
	}
	return ("Tractor beam broken, Captain.")
}

// cleanupShip handles all cleanup necessary when a ship is removed from the game (quit or inactivity)
func (i *Interpreter) cleanupShip(ship *Object) {
	i.spatialIndexMutex.Lock()
	i.cleanupShipNoLock(ship)
	i.spatialIndexMutex.Unlock()

	// Refresh all ship pointers after slice modification to prevent dangling pointers
	// Must be called after releasing the lock to avoid deadlock
	i.refreshShipPointers()
}

// cleanupShipNoLock performs ship cleanup assuming i.spatialIndexMutex is already held.
// Only call this if you already hold the lock!
func (i *Interpreter) cleanupShipNoLock(ship *Object) {
	if ship == nil {
		return
	}

	// --- Tractor beam cleanup start ---
	// Handle cleanup for all tractor beam relationships involving this ship
	for idx := range i.objects {
		other := i.objects[idx]
		if other.Type != "Ship" || other.Galaxy != ship.Galaxy || other.Name == ship.Name {
			continue
		}

		// Case 1: This ship is tractoring another ship
		if ship.TractorOnOff && ship.TractorShip != "" && other.Name == ship.TractorShip {
			other.TractorOnOff = false
			other.TractorShip = ""
			// Notify the other ship that the tractor beam is broken
			i.notifyShipTractorBroken(other.Name, other.Galaxy)
		}

		// Case 2: Another ship is tractoring this ship
		if other.TractorOnOff && other.TractorShip == ship.Name {
			other.TractorOnOff = false
			other.TractorShip = ""
			// Notify the other ship that the tractor beam is broken
			i.notifyShipTractorBroken(other.Name, other.Galaxy)
		}
	}

	// Clear this ship's tractor state
	ship.TractorOnOff = false
	ship.TractorShip = ""
	// --- Tractor beam cleanup end ---

	// Remove the ship from the objects slice and spatial indexes
	if ship.EnteredTime != nil {
		ship.EnteredTime = nil
	}
	// Inline removal logic from removeObjectByIndex
	var removeIdx = -1
	for j := range i.objects {
		if i.objects[j] == ship {
			removeIdx = j
			break
		}
	}
	if removeIdx < 0 || removeIdx >= len(i.objects) {
		return
	}

	// Remove from spatial indexes first
	obj := i.objects[removeIdx]
	galaxy := obj.Galaxy

	if i.objectsByLocation[galaxy] != nil {
		// Remove from location index
		locKey := formatLocationKey(obj.LocationX, obj.LocationY)
		delete(i.objectsByLocation[galaxy], locKey)

		// Remove from type index
		if typeSlice, exists := i.objectsByType[galaxy][obj.Type]; exists {
			for idx, o := range typeSlice {
				if o == obj {
					// Remove by replacing with last element and truncating
					typeSlice[idx] = typeSlice[len(typeSlice)-1]
					i.objectsByType[galaxy][obj.Type] = typeSlice[:len(typeSlice)-1]
					break
				}
			}
		}

		// Remove from ship name index if it's a ship
		if obj.Type == "Ship" && obj.Name != "" {
			delete(i.shipsByGalaxyAndName[galaxy], obj.Name)
		}
	}

	// Remove from objects slice
	i.objects = append(i.objects[:removeIdx], i.objects[removeIdx+1:]...)

	// Rebuild all pointers to ensure they point to the new slice position
	// Clear existing indexes
	i.objectsByLocation = make(map[uint16]map[string]*Object)
	i.objectsByType = make(map[uint16]map[string][]*Object)
	i.shipsByGalaxyAndName = make(map[uint16]map[string]*Object)

	// Rebuild from objects slice - use range to avoid slice modification issues
	for _, obj := range i.objects {
		if obj == nil {
			continue
		}
		galaxy := obj.Galaxy

		// Initialize galaxy maps if needed
		if i.objectsByLocation[galaxy] == nil {
			i.objectsByLocation[galaxy] = make(map[string]*Object)
		}
		if i.objectsByType[galaxy] == nil {
			i.objectsByType[galaxy] = make(map[string][]*Object)
		}
		if i.shipsByGalaxyAndName[galaxy] == nil {
			i.shipsByGalaxyAndName[galaxy] = make(map[string]*Object)
		}

		// Add to location index
		locKey := formatLocationKey(obj.LocationX, obj.LocationY)
		i.objectsByLocation[galaxy][locKey] = obj

		// Add to type index
		i.objectsByType[galaxy][obj.Type] = append(i.objectsByType[galaxy][obj.Type], obj)

		// Add to ship name index if it's a ship
		if obj.Type == "Ship" && obj.Name != "" {
			i.shipsByGalaxyAndName[galaxy][obj.Name] = obj
		}
	}
}

// notifyShipTractorBroken sends a "Tractor beam broken" message to a specific ship
func (i *Interpreter) notifyShipTractorBroken(shipName string, galaxy uint16) {
	i.connections.Range(func(key, value interface{}) bool {
		otherConn := key.(net.Conn)
		otherConnInfo := value.(ConnectionInfo)
		if otherConnInfo.Shipname == shipName && otherConnInfo.Galaxy == galaxy {
			if writerRaw, ok := i.writers.Load(otherConn); ok {
				writer := writerRaw.(*bufio.Writer)
				i.writeBaudf(otherConn, writer, "Tractor beam broken, Captain.\r\n")
				prompt := i.getPrompt(otherConn)
				if mutexRaw, ok := i.writerMutexs.Load(otherConn); ok {
					mutex := mutexRaw.(*sync.Mutex)
					mutex.Lock()
					writer.WriteString(prompt)
					writer.Flush()
					mutex.Unlock()
				}
			}
			return false // Stop iteration
		}
		return true // Continue iteration
	})
}

// tractorOn is a helper method of Interpreter that returns a simple string.
func (i *Interpreter) tractorOn(conn net.Conn, whoToTract string) string {
	var obj *Object
	var other *Object
	var info interface{}
	var ok bool
	var connInfo ConnectionInfo
	var myObjX int
	var myObjY int
	var objFound int

	// My tractor beam alreay active?  Also check shields
	if info, ok = i.connections.Load(conn); ok {
		connInfo = info.(ConnectionInfo)
		if connInfo.Shipname != "" {
			for idx := range i.objects {
				obj = i.objects[idx]
				if obj.Type == "Ship" && obj.Name == connInfo.Shipname && obj.Galaxy == connInfo.Galaxy {
					myObjX = obj.LocationX //used in adjacency
					myObjY = obj.LocationY
					if obj.ShieldsUpDown == true {
						return ("Can not apply tractor beam through shields, Captain.")
					}
					if obj.TractorOnOff == true {
						return ("Tractor beam already active, Captain.")
					}
					break // Stop loop after finding the player's ship
				}
			}

			//Find other ship
			for j := range i.objects {
				other = i.objects[j]
				if other.Type == "Ship" && other.Name == whoToTract && other.Galaxy == connInfo.Galaxy { //Found object
					objFound = j
					continue
				}
			}
		}
	}
	other = i.objects[objFound]
	// Check for adjacency
	if (math.Abs(float64(other.LocationX - myObjX))) > 1 {
		return ("Not adjacent to destination ship.")
	}
	if (math.Abs(float64(other.LocationY - myObjY))) > 1 {
		return ("Not adjacent to destination ship.")
	}
	//Rules change for gowars side must be same & type = ship
	if !(DecwarMode == true && other.Side == obj.Side && other.Type == "Ship") {
		return ("Can not apply tractor beam to enemy ship.")
	}

	if whoToTract == connInfo.Shipname {
		return ("Beg your pardon, Captain?  You want to apply a tractor beam to your own ship?")
	}

	if other.ShieldsUpDown == true {
		return (other.Name + " has his shields up.  Unable to apply tractor beam.")
	}

	// Turn on the tractor for both objects
	obj.TractorOnOff = true
	obj.TractorShip = whoToTract
	other.TractorOnOff = true
	other.TractorShip = connInfo.Shipname

	//Send a message to the other ship to report tractor being established
	i.notifyShipTractorActivated(whoToTract, connInfo.Galaxy)

	return (whoToTract + " is being tractored")
}

// notifyShipTractorActivated sends a "Tractor beam activated" message to a specific ship
func (i *Interpreter) notifyShipTractorActivated(shipName string, galaxy uint16) {
	i.connections.Range(func(key, value interface{}) bool {
		otherConn := key.(net.Conn)
		otherConnInfo := value.(ConnectionInfo)
		if otherConnInfo.Shipname == shipName && otherConnInfo.Galaxy == galaxy {
			if writerRaw, ok := i.writers.Load(otherConn); ok {
				writer := writerRaw.(*bufio.Writer)
				i.writeBaudf(otherConn, writer, "Tractor beam activated, Captain.\r\n")
				prompt := i.getPrompt(otherConn)
				if mutexRaw, ok := i.writerMutexs.Load(otherConn); ok {
					mutex := mutexRaw.(*sync.Mutex)
					mutex.Lock()
					writer.WriteString(prompt)
					writer.Flush()
					mutex.Unlock()
				}
			}
			return false // Stop iteration
		}
		return true // Continue iteration
	})
}

// cleanupShipTractorBeams handles tractor beam cleanup for a specific ship without removing the ship from objects
func (i *Interpreter) cleanupShipTractorBeams(ship *Object) {
	if ship == nil {
		return
	}

	// Handle cleanup for all tractor beam relationships involving this ship
	for idx := range i.objects {
		other := i.objects[idx]
		if other.Galaxy != ship.Galaxy || other.Name == ship.Name {
			continue
		}

		// Case 1: This ship is tractoring another ship
		if ship.TractorOnOff && ship.TractorShip != "" && other.Name == ship.TractorShip {
			other.TractorOnOff = false
			other.TractorShip = ""
			// Notify the other ship that the tractor beam is broken
			i.notifyShipTractorBroken(other.Name, other.Galaxy)
		}

		// Case 2: Another ship is tractoring this ship
		if other.TractorOnOff && other.TractorShip == ship.Name {
			other.TractorOnOff = false
			other.TractorShip = ""
			// Notify the other ship that the tractor beam is broken
			i.notifyShipTractorBroken(other.Name, other.Galaxy)
		}
	}

	// Clear this ship's tractor state
	ship.TractorOnOff = false
	ship.TractorShip = ""
}

func (i *Interpreter) damagesMediumStub(args []string, conn net.Conn) string {
	// Medium abbreviations
	mediumParams := []string{
		"Shields", "Warp", "Impulse", "Life Sup", "Torps", "Phasers", "Computer", "Radio", "Tractor",
	}
	paramMap := map[string]string{
		"shields":         "Shields",
		"warp engines":    "Warp",
		"impulse engines": "Impulse",
		"life support":    "Life Sup",
		"torpedo tubes":   "Torps",
		"phasers":         "Phasers",
		"computer":        "Computer",
		"radio":           "Radio",
		"tractor beam":    "Tractor",
	}
	abbrMap := map[string]string{
		"shields":  "sh",
		"warp":     "wa",
		"impulse":  "im",
		"life sup": "ls",
		"torps":    "to",
		"phasers":  "ph",
		"computer": "co",
		"radio":    "ra",
		"tractor":  "tr",
	}
	// Find user's ship
	var shipObj *Object
	if info, ok := i.connections.Load(conn); ok {
		connInfo := info.(ConnectionInfo)
		shipname := connInfo.Shipname
		galaxy := connInfo.Galaxy
		for idx := range i.objects {
			obj := i.objects[idx]
			if obj.Type == "Ship" && obj.Name == shipname && obj.Galaxy == galaxy {
				shipObj = obj
				break
			}
		}
	}
	// Tab completion and parameter prompting
	if len(args) == 0 {
		// Check if all devices are functional (all damage = 0)
		if shipObj != nil {
			totalDamage := shipObj.ShieldsDamage + shipObj.WarpEnginesDamage + shipObj.ImpulseEnginesDamage +
				shipObj.LifeSupportDamage + shipObj.TorpedoTubeDamage + shipObj.PhasersDamage +
				shipObj.ComputerDamage + shipObj.RadioDamage + shipObj.TractorDamage
			if totalDamage == 0 {
				return "All devices functional."
			}
		}

		var stubs []string
		for _, param := range mediumParams {
			if param == "Shields" && shipObj != nil {
				stubs = append(stubs, fmt.Sprintf("Shields: \t%d", shipObj.ShieldsDamage))
			} else if param == "Warp" && shipObj != nil {
				stubs = append(stubs, fmt.Sprintf("Warp: \t\t%d", shipObj.WarpEnginesDamage))
			} else if param == "Impulse" && shipObj != nil {
				stubs = append(stubs, fmt.Sprintf("Impulse: \t%d", shipObj.ImpulseEnginesDamage))
			} else if param == "Life Sup" && shipObj != nil {
				stubs = append(stubs, fmt.Sprintf("Life Sup: \t%d", shipObj.LifeSupportDamage))
			} else if param == "Torps" && shipObj != nil {
				stubs = append(stubs, fmt.Sprintf("Torps: \t\t%d", shipObj.TorpedoTubeDamage))
			} else if param == "Phasers" && shipObj != nil {
				stubs = append(stubs, fmt.Sprintf("Phasers: \t%d", shipObj.PhasersDamage))
			} else if param == "Computer" && shipObj != nil {
				stubs = append(stubs, fmt.Sprintf("Computer: \t%d", shipObj.ComputerDamage))
			} else if param == "Radio" && shipObj != nil {
				stubs = append(stubs, fmt.Sprintf("Radio: \t\t%d", shipObj.RadioDamage))
			} else if param == "Tractor" && shipObj != nil {
				stubs = append(stubs, fmt.Sprintf("Tractor: \t%d", shipObj.TractorDamage))
			} else {
				stubs = append(stubs, fmt.Sprintf("%s:", param))
			}
		}
		return strings.Join(stubs, "\r\n")
	}
	if len(args) == 1 && strings.HasSuffix(args[0], "?") {
		prefix := strings.ToLower(strings.TrimSuffix(args[0], "?"))
		var matches []string
		for _, param := range mediumParams {
			abbr := abbrMap[strings.ToLower(param)]
			if strings.HasPrefix(strings.ToLower(param), prefix) || strings.HasPrefix(abbr, prefix) {
				matches = append(matches, param)
			}
		}
		if len(matches) == 0 {
			return "Error: No valid completion for damages parameter"
		}
		return "damages " + strings.Join(matches, " | ")
	}
	var stubs []string
	used := make(map[string]bool)
	for _, arg := range args {
		input := strings.ToLower(arg)
		var matches []string
		for full, abbr := range paramMap {
			if strings.HasPrefix(full, input) || strings.HasPrefix(strings.ToLower(abbr), input) {
				matches = append(matches, abbr)
			}
		}
		if len(matches) == 0 {
			stubs = append(stubs, fmt.Sprintf("Error: Unknown damages parameter '%s'.", arg))
		} else if len(matches) > 1 {
			stubs = append(stubs, fmt.Sprintf("Error: Ambiguous damages parameter '%s'. Please be more specific.", arg))
		} else if !used[matches[0]] {
			if matches[0] == "SH" && shipObj != nil {
				stubs = append(stubs, fmt.Sprintf("SH: %d", shipObj.ShieldsDamage))
			} else if matches[0] == "WA" && shipObj != nil {
				stubs = append(stubs, fmt.Sprintf("WA: %d", shipObj.WarpEnginesDamage))
			} else if matches[0] == "IM" && shipObj != nil {
				stubs = append(stubs, fmt.Sprintf("IM: %d", shipObj.ImpulseEnginesDamage))
			} else if matches[0] == "LS" && shipObj != nil {
				stubs = append(stubs, fmt.Sprintf("LS: %d", shipObj.LifeSupportDamage))
			} else if matches[0] == "TO" && shipObj != nil {
				stubs = append(stubs, fmt.Sprintf("TO: %d", shipObj.TorpedoTubeDamage))
			} else if matches[0] == "PH" && shipObj != nil {
				stubs = append(stubs, fmt.Sprintf("PH: %d", shipObj.PhasersDamage))
			} else if matches[0] == "CO" && shipObj != nil {
				stubs = append(stubs, fmt.Sprintf("CO: %d", shipObj.ComputerDamage))
			} else if matches[0] == "RA" && shipObj != nil {
				stubs = append(stubs, fmt.Sprintf("RA: %d", shipObj.RadioDamage))
			} else if matches[0] == "TR" && shipObj != nil {
				stubs = append(stubs, fmt.Sprintf("TR: %d", shipObj.TractorDamage))
			} else {
				stubs = append(stubs, fmt.Sprintf("%s:", matches[0]))
			}
			used[matches[0]] = true
		}
	}
	return strings.Join(stubs, "\r\n")
}

// Damages stub for short OutputState
func (i *Interpreter) damagesShortStub(args []string, conn net.Conn) string {
	// Short abbreviations
	shortParams := []string{
		"SH", "WA", "IM", "LS", "TO", "PH", "CO", "RA", "TR",
	}
	paramMap := map[string]string{
		"shields":         "SH",
		"warp engines":    "WA",
		"impulse engines": "IM",
		"life support":    "LS",
		"torpedo tubes":   "TO",
		"phasers":         "PH",
		"computer":        "CO",
		"radio":           "RA",
		"tractor beam":    "TR",
	}
	abbrMap := map[string]string{
		"sh": "sh",
		"wa": "wa",
		"im": "im",
		"ls": "ls",
		"to": "to",
		"ph": "ph",
		"co": "co",
		"ra": "ra",
		"tr": "tr",
	}

	// Find user's ship
	var shipObj *Object
	if info, ok := i.connections.Load(conn); ok {
		connInfo := info.(ConnectionInfo)
		shipname := connInfo.Shipname
		galaxy := connInfo.Galaxy
		for idx := range i.objects {
			obj := i.objects[idx]
			if obj.Type == "Ship" && obj.Name == shipname && obj.Galaxy == galaxy {
				shipObj = obj
				break
			}
		}
	}

	// Tab completion and parameter prompting
	if len(args) == 0 {
		// Check if all devices are functional (all damage = 0)
		if shipObj != nil {
			totalDamage := shipObj.ShieldsDamage + shipObj.WarpEnginesDamage + shipObj.ImpulseEnginesDamage +
				shipObj.LifeSupportDamage + shipObj.TorpedoTubeDamage + shipObj.PhasersDamage +
				shipObj.ComputerDamage + shipObj.RadioDamage + shipObj.TractorDamage
			if totalDamage == 0 {
				return "All devices functional."
			}
		}

		var stubs []string
		for _, param := range shortParams {
			if param == "SH" && shipObj != nil {
				stubs = append(stubs, fmt.Sprintf("SH: %d", shipObj.ShieldsDamage))
			} else if param == "WA" && shipObj != nil {
				stubs = append(stubs, fmt.Sprintf("WA: %d", shipObj.WarpEnginesDamage))
			} else if param == "IM" && shipObj != nil {
				stubs = append(stubs, fmt.Sprintf("IM: %d", shipObj.ImpulseEnginesDamage))
			} else if param == "LS" && shipObj != nil {
				stubs = append(stubs, fmt.Sprintf("LS: %d", shipObj.LifeSupportDamage))
			} else if param == "TO" && shipObj != nil {
				stubs = append(stubs, fmt.Sprintf("TO: %d", shipObj.TorpedoTubeDamage))
			} else if param == "PH" && shipObj != nil {
				stubs = append(stubs, fmt.Sprintf("PH: %d", shipObj.PhasersDamage))
			} else if param == "CO" && shipObj != nil {
				stubs = append(stubs, fmt.Sprintf("CO: %d", shipObj.ComputerDamage))
			} else if param == "RA" && shipObj != nil {
				stubs = append(stubs, fmt.Sprintf("RA: %d", shipObj.RadioDamage))
			} else if param == "TR" && shipObj != nil {
				stubs = append(stubs, fmt.Sprintf("TR: %d", shipObj.TractorDamage))
			} else {
				stubs = append(stubs, fmt.Sprintf("%s:", param))
			}
		}
		return strings.Join(stubs, "\r\n")
	}
	if len(args) == 1 && strings.HasSuffix(args[0], "?") {
		prefix := strings.ToLower(strings.TrimSuffix(args[0], "?"))
		var matches []string
		for _, param := range shortParams {
			abbr := abbrMap[strings.ToLower(param)]
			if strings.HasPrefix(strings.ToLower(param), prefix) || strings.HasPrefix(abbr, prefix) {
				matches = append(matches, param)
			}
		}
		if len(matches) == 0 {
			return "Error: No valid completion for damages parameter"
		}
		return "damages " + strings.Join(matches, " | ")
	}
	var stubs []string
	used := make(map[string]bool)
	for _, arg := range args {
		input := strings.ToLower(arg)
		var matches []string
		for full, abbr := range paramMap {
			if strings.HasPrefix(full, input) || strings.HasPrefix(strings.ToLower(abbr), input) {
				matches = append(matches, abbr)
			}
		}
		if len(matches) == 0 {
			stubs = append(stubs, fmt.Sprintf("Error: Unknown damages parameter '%s'.", arg))
		} else if len(matches) > 1 {
			stubs = append(stubs, fmt.Sprintf("Error: Ambiguous damages parameter '%s'. Please be more specific.", arg))
		} else if !used[matches[0]] {
			if matches[0] == "SH" && shipObj != nil {
				stubs = append(stubs, fmt.Sprintf("SH: %d", shipObj.ShieldsDamage))
			} else if matches[0] == "WA" && shipObj != nil {
				stubs = append(stubs, fmt.Sprintf("WA: %d", shipObj.WarpEnginesDamage))
			} else {
				stubs = append(stubs, fmt.Sprintf("%s:", matches[0]))
			}
			used[matches[0]] = true
		}
	}
	return strings.Join(stubs, "\r\n")
}

// runHandlerWithContext wraps a synchronous CommandHandler so it respects
// context cancellation.  The handler runs in a goroutine; if the context
// is cancelled before the handler returns, "[Output interrupted]" is
// returned immediately.
func (i *Interpreter) runHandlerWithContext(ctx context.Context, handler CommandHandler, args []string, conn net.Conn) string {
	select {
	case <-ctx.Done():
		return "[Output interrupted]"
	default:
	}

	resultChan := make(chan string, 1)
	go func() {
		resultChan <- handler(args, conn)
	}()

	select {
	case <-ctx.Done():
		return "[Output interrupted]"
	case result := <-resultChan:
		return result
	}
}

func (i *Interpreter) handleListCtx(ctx context.Context, args []string, conn net.Conn) string {
	return i.runHandlerWithContext(ctx, i.gowarsCommands["list"].Handler, args, conn)
}

func (i *Interpreter) handleTargetsCtx(ctx context.Context, args []string, conn net.Conn) string {
	return i.runHandlerWithContext(ctx, i.gowarsCommands["targets"].Handler, args, conn)
}

func (i *Interpreter) handleDamagesCtx(ctx context.Context, args []string, conn net.Conn) string {
	return i.runHandlerWithContext(ctx, i.gowarsCommands["damages"].Handler, args, conn)
}

// Stub to process 'status' parameter after docking
func (i *Interpreter) processDockStatus(conn net.Conn, ship *Object) {
	// Show the status for the user's ship when 'status' is entered in dock command context
	status := i.handleStatus([]string{}, conn)
	if status != "" {
		conn.Write([]byte(status))
	}
}

// Stub to process each device parameter after docking
func (i *Interpreter) processDockDevice(conn net.Conn, ship *Object, dockedObj *Object, device string) {
	// Standardized DECWAR device repair logic for base/planet
	const (
		BaseDeviceRepair   = 10
		PlanetDeviceRepair = 5
	)
	if dockedObj == nil {
		return
	}
	isBase := dockedObj.Type == "Base"
	isPlanet := dockedObj.Type == "Planet"

	switch device {
	case "warp":
		if isBase {
			if ship.WarpEnginesDamage > BaseDeviceRepair {
				ship.WarpEnginesDamage -= BaseDeviceRepair
			} else {
				ship.WarpEnginesDamage = 0
			}
		} else if isPlanet {
			if ship.WarpEnginesDamage > PlanetDeviceRepair {
				ship.WarpEnginesDamage -= PlanetDeviceRepair
			} else {
				ship.WarpEnginesDamage = 0
			}
		}
	case "impulse":
		if isBase {
			if ship.ImpulseEnginesDamage > BaseDeviceRepair {
				ship.ImpulseEnginesDamage -= BaseDeviceRepair
			} else {
				ship.ImpulseEnginesDamage = 0
			}
		} else if isPlanet {
			if ship.ImpulseEnginesDamage > PlanetDeviceRepair {
				ship.ImpulseEnginesDamage -= PlanetDeviceRepair
			} else {
				ship.ImpulseEnginesDamage = 0
			}
		}
	case "torpedos":
		if isBase {
			if ship.TorpedoTubeDamage > BaseDeviceRepair {
				ship.TorpedoTubeDamage -= BaseDeviceRepair
			} else {
				ship.TorpedoTubeDamage = 0
			}
		} else if isPlanet {
			if ship.TorpedoTubeDamage > PlanetDeviceRepair {
				ship.TorpedoTubeDamage -= PlanetDeviceRepair
			} else {
				ship.TorpedoTubeDamage = 0
			}
		}
	case "phasers":
		if isBase {
			if ship.PhasersDamage > BaseDeviceRepair {
				ship.PhasersDamage -= BaseDeviceRepair
			} else {
				ship.PhasersDamage = 0
			}
		} else if isPlanet {
			if ship.PhasersDamage > PlanetDeviceRepair {
				ship.PhasersDamage -= PlanetDeviceRepair
			} else {
				ship.PhasersDamage = 0
			}
		}
	case "shields":
		if isBase {
			if ship.ShieldsDamage > BaseDeviceRepair {
				ship.ShieldsDamage -= BaseDeviceRepair
			} else {
				ship.ShieldsDamage = 0
			}
		} else if isPlanet {
			if ship.ShieldsDamage > PlanetDeviceRepair {
				ship.ShieldsDamage -= PlanetDeviceRepair
			} else {
				ship.ShieldsDamage = 0
			}
		}
	case "computer":
		if isBase {
			if ship.ComputerDamage > BaseDeviceRepair {
				ship.ComputerDamage -= BaseDeviceRepair
			} else {
				ship.ComputerDamage = 0
			}
		} else if isPlanet {
			if ship.ComputerDamage > PlanetDeviceRepair {
				ship.ComputerDamage -= PlanetDeviceRepair
			} else {
				ship.ComputerDamage = 0
			}
		}
	case "lifesupport":
		if isBase {
			if ship.LifeSupportDamage > BaseDeviceRepair {
				ship.LifeSupportDamage -= BaseDeviceRepair
			} else {
				ship.LifeSupportDamage = 0
			}
		} else if isPlanet {
			if ship.LifeSupportDamage > PlanetDeviceRepair {
				ship.LifeSupportDamage -= PlanetDeviceRepair
			} else {
				ship.LifeSupportDamage = 0
			}
		}
	case "radio":
		if isBase {
			if ship.RadioDamage > BaseDeviceRepair {
				ship.RadioDamage -= BaseDeviceRepair
			} else {
				ship.RadioDamage = 0
			}
		} else if isPlanet {
			if ship.RadioDamage > PlanetDeviceRepair {
				ship.RadioDamage -= PlanetDeviceRepair
			} else {
				ship.RadioDamage = 0
			}
		}
	case "tractor":
		if isBase {
			if ship.TractorDamage > BaseDeviceRepair {
				ship.TractorDamage -= BaseDeviceRepair
			} else {
				ship.TractorDamage = 0
			}
		} else if isPlanet {
			if ship.TractorDamage > PlanetDeviceRepair {
				ship.TractorDamage -= PlanetDeviceRepair
			} else {
				ship.TractorDamage = 0
			}
		}
	default:
	}
}

// handleTorpedo2Args handles 2-argument torpedo commands
func (i *Interpreter) handleTorpedo2Args(args []string, conn net.Conn, connInfo ConnectionInfo) string {
	// Check if first argument is "computed" mode
	validModes := map[string]bool{"computed": true}
	if mode, ok := i.resolveParameter(strings.ToLower(args[0]), validModes); ok && mode == "computed" {
		return i.handleTorpedoComputed(args[1], conn, connInfo.Galaxy, 1)
	}

	// Default: treat as vpos/hpos using ICdef
	vpos, hpos, err := i.parseCoordinates(args[0], args[1], conn, false)
	if err != nil {
		return "Invalid coordinates: " + err.Error()
	}

	coordArgs := []string{strconv.Itoa(vpos), strconv.Itoa(hpos)}
	return i.torpedoSimple("simple", coordArgs, conn, 1)
}

// handleTorpedo3Args handles 3-argument torpedo commands
func (i *Interpreter) handleTorpedo3Args(args []string, conn net.Conn, connInfo ConnectionInfo) string {
	firstArg := strings.ToLower(args[0])

	// Check if first argument is "computed" (with abbreviation support)
	validComputedModes := map[string]bool{"computed": true}
	if mode, ok := i.resolveParameter(firstArg, validComputedModes); ok && mode == "computed" {
		numTorps := 1
		if num, err := strconv.Atoi(args[1]); err == nil {
			numTorps = num
			return i.handleTorpedoComputed(args[2], conn, connInfo.Galaxy, numTorps)
		}
		return i.handleTorpedoComputed(args[1], conn, connInfo.Galaxy, numTorps)
	}

	// Check if first argument is a number (numTorps with ICdef mode)
	if numTorps, err := strconv.Atoi(args[0]); err == nil {
		return i.torpedoSimple(connInfo.ICdef, args[1:], conn, numTorps)
	}

	// Check if first argument is explicit mode (absolute/relative)
	validModes := map[string]bool{"absolute": true, "relative": true}
	if mode, ok := i.resolveParameter(firstArg, validModes); ok {
		return i.torpedoSimple(mode, args[1:], conn, 1)
	}

	return "First argument must be either a number, 'computed', 'absolute', or 'relative'"
}

// handleTorpedoComputed finds a ship by name and fires torpedos at it
func (i *Interpreter) handleTorpedoComputed(shipname string, conn net.Conn, galaxy uint16, numTorps int) string {
	// Find the closest matching ship within MaxRange for computed targeting
	abbr := strings.ToLower(shipname)

	var myShip *Object
	for idx := range i.objects {
		obj := i.objects[idx]
		if obj.Galaxy == galaxy && strings.EqualFold(obj.Type, "Ship") {
			info, ok := i.connections.Load(conn)
			if ok && obj.Name == info.(ConnectionInfo).Shipname {
				myShip = obj
				break
			}
		}
	}
	if myShip == nil {
		return "Error: unable to determine your ship."
	}

	var bestTarget *Object
	bestDist := MaxRange + 1
	for idx := range i.objects {
		obj := i.objects[idx]
		if !strings.EqualFold(obj.Type, "Ship") || obj == myShip || obj.Galaxy != galaxy {
			continue
		}
		if strings.HasPrefix(strings.ToLower(obj.Name), abbr) {
			dx := AbsInt(obj.LocationX - myShip.LocationX)
			dy := AbsInt(obj.LocationY - myShip.LocationY)
			dist := dx
			if dy > dx {
				dist = dy
			}
			if dist <= MaxRange && dist < bestDist {
				bestTarget = obj
				bestDist = dist
			}
		}
	}
	if bestTarget == nil {
		return "Target out of range."
	}
	args := []string{strconv.Itoa(bestTarget.LocationX), strconv.Itoa(bestTarget.LocationY)}
	return i.torpedoSimple("absolute", args, conn, numTorps)
}

// handleTorpedo4Args handles 4-argument torpedo commands: tor <mode> <numtorps> <vpos> <hpos>
func (i *Interpreter) handleTorpedo4Args(args []string, conn net.Conn, connInfo ConnectionInfo) string {
	firstArg := strings.ToLower(args[0])

	// Check if first argument is a valid mode (absolute, relative, or computed)
	validModes := map[string]bool{"absolute": true, "relative": true, "computed": true}
	mode, ok := i.resolveParameter(firstArg, validModes)
	if !ok {
		return "First argument must be 'absolute', 'relative', or 'computed'"
	}

	// Parse number of torpedos
	numTorps, err := strconv.Atoi(args[1])
	if err != nil {
		return "Second argument must be the number of torpedos (integer)"
	}

	if numTorps < 1 {
		return "Number of torpedos must be at least 1"
	}

	// Handle computed mode differently (target is ship name)
	if mode == "computed" {
		return i.handleTorpedoComputed(args[2], conn, connInfo.Galaxy, numTorps)
	}

	// For absolute and relative modes, parse coordinates
	coordArgs := []string{args[2], args[3]}
	return i.torpedoSimple(mode, coordArgs, conn, numTorps)
}

// calculateTorpedoDeflection calculates torpedo deflection based on firing ship's condition
func (i *Interpreter) calculateTorpedoDeflection(attacker *Object, rng *rand.Rand) float64 {
	// Base deflection
	d := (rng.Float64() - 0.5) / 5.0

	// Additional deflection if torpedo tubes OR computer damaged
	if attacker.TorpedoTubeDamage > 0 || attacker.ComputerDamage > 0 {
		d += (rng.Float64() - 0.5) / 10.0
	}

	// Shield interference if shields are up
	if attacker.ShieldsUpDown && attacker.Shields > 0 {
		shieldPercent := float64(attacker.Shields) / float64(InitialShieldValue)
		d += (shieldPercent * 1000.0 * (rng.Float64() - 0.5)) / 10000.0
	}

	return d
}

// torpedoPathLocked performs torpedo path calculations without acquiring the objects mutex.
func (i *Interpreter) torpedoPathLocked(shipX, shipY, targetX, targetY int, galaxy uint16, deflection float64) (int, bool, int, int) {
	// Calculate direction vector from ship to target
	dx := targetX - shipX
	dy := targetY - shipY

	// Apply deflection perpendicular to the line of fire
	distanceF := math.Sqrt(float64(dx*dx + dy*dy))
	if distanceF > 0 {
		perpX := -float64(dy) / distanceF
		perpY := float64(dx) / distanceF

		deflectX := int(perpX * deflection * distanceF)
		deflectY := int(perpY * deflection * distanceF)

		targetX += deflectX
		targetY += deflectY

		// Recalculate direction vector after deflection
		dx = targetX - shipX
		dy = targetY - shipY
	}

	// Calculate the distance to the target
	distance := max(AbsInt(dx), AbsInt(dy))

	// Always calculate a point 10 units away in the target direction
	var endX, endY int
	if distance == 0 {
		// If target is same as ship, torpedo doesn't move
		endX, endY = shipX, shipY
	} else {
		// Normalize direction and scale to 10 units
		// Use floating point for precision, then convert to int
		factor := 10.0 / float64(distance)
		endX = shipX + int(math.Round(float64(dx)*factor))
		endY = shipY + int(math.Round(float64(dy)*factor))
	}

	// Calculate torpedo path using Bresenham's Line Algorithm (always 10 units)
	path := i.bresenhamLine(shipX, shipY, endX, endY)

	var closestObjectIdx int = -1
	var closestDistance int = MaxRange + 1
	var objectFound bool = false

	// Loop through each point in the torpedo path
	for _, point := range path {
		x, y := point[0], point[1]
		// Check if any object exists at this coordinate
		for idx, obj := range i.objects {
			if obj.Galaxy == galaxy && obj.LocationX == x && obj.LocationY == y {
				// Calculate distance from ship to this object
				distance := max(AbsInt(shipX-x), AbsInt(shipY-y))

				// If this object is closer than previous found objects, update closest
				if distance < closestDistance {
					closestDistance = distance
					closestObjectIdx = idx
					objectFound = true
				}
			}
		}
	}

	return closestObjectIdx, objectFound, endX, endY
}

// bresenhamLine implements Bresenham's Line Algorithm to get all points along a line
func (i *Interpreter) bresenhamLine(x0, y0, x1, y1 int) [][2]int {
	var points [][2]int

	dx := AbsInt(x1 - x0)
	dy := AbsInt(y1 - y0)

	x, y := x0, y0

	var xStep, yStep int
	if x0 < x1 {
		xStep = 1
	} else {
		xStep = -1
	}

	if y0 < y1 {
		yStep = 1
	} else {
		yStep = -1
	}

	if dx > dy {
		// X-major case
		err := dx / 2
		for x != x1 {
			x += xStep
			err -= dy
			if err < 0 {
				y += yStep
				err += dx
			}
			points = append(points, [2]int{x, y})
		}
	} else {
		// Y-major case
		err := dy / 2
		for y != y1 {
			y += yStep
			err -= dx
			if err < 0 {
				x += xStep
				err += dy
			}
			points = append(points, [2]int{x, y})
		}
	}

	return points
}

// torpedoSimple handles simple vpos hpos torpedo targeting
func (i *Interpreter) torpedoSimple(mode string, args []string, conn net.Conn, numTorps int) string {
	// Default mode if not specified - use actual implementation
	if mode == "" {
		mode = "simple"
	}

	energy := 0
	vpos := 0
	hpos := 0
	//	shipname := ""
	var err error
	var galaxy uint16

	// Get galaxy
	info, ok := i.connections.Load(conn)
	if ok {
		galaxy = info.(ConnectionInfo).Galaxy
	}

	// --- OVERRIDE ICdef if targeting mode is specified ---
	if mode == "computed" {
		// Computed mode: [numTorps] <shipname>
		if len(args) == 0 {
			return "Computed torpedo mode requires parameters: <shipname> [NumTorps]"
		}

		// Handle optional number of torpedoes as first argument
		shipname := ""
		if len(args) == 1 {
			shipname = args[0]
		} else if len(args) == 2 {
			// Try to parse first argument as number of torpedoes
			if n, err := strconv.Atoi(args[0]); err == nil {
				numTorps = n
				shipname = args[1]
			} else {
				shipname = args[0]
			}
		} else {
			return "Invalid syntax for computed mode. Usage: torpedos computed [numTorps] <shipname>"
		}
		abbr := strings.ToLower(shipname)

		// Check if attacker's computer has more than CriticalDamage
		info, ok := i.connections.Load(conn)
		if ok {
			connInfo := info.(ConnectionInfo)
			for idx := range i.objects {
				obj := i.objects[idx]
				if obj.Type == "Ship" && obj.Name == connInfo.Shipname && obj.Galaxy == connInfo.Galaxy {
					if obj.ComputerDamage > CriticalDamage {
						return "Computer inoperative."
					}
					break
				}
			}
		}

		// Modified computed targeting: only consider ships within MaxRange in the same galaxy,
		// prefer the closest one (smallest Chebyshev distance). If none, report out of range.
		var myShip *Object
		for idx := range i.objects {
			obj := i.objects[idx]
			if strings.EqualFold(obj.Type, "Ship") && obj.Name == info.(ConnectionInfo).Shipname && obj.Galaxy == galaxy {
				myShip = obj
				break
			}
		}
		if myShip == nil {
			return "Error: unable to determine your ship."
		}

		bestTarget := (*Object)(nil)
		bestDist := MaxRange + 1
		for idx := range i.objects {
			obj := i.objects[idx]
			if !strings.EqualFold(obj.Type, "Ship") || obj == myShip || obj.Galaxy != galaxy {
				continue
			}
			if strings.HasPrefix(strings.ToLower(obj.Name), abbr) {
				dx := AbsInt(obj.LocationX - myShip.LocationX)
				dy := AbsInt(obj.LocationY - myShip.LocationY)
				dist := dx
				if dy > dx {
					dist = dy
				}
				if dist <= MaxRange && dist < bestDist {
					bestTarget = obj
					bestDist = dist
				}
			}
		}
		if bestTarget == nil {
			return "Target out of range."
		}
		vpos = bestTarget.LocationX
		hpos = bestTarget.LocationY

		// Continue with firing logic below
	} else if mode == "absolute" || mode == "relative" {
		// Absolute or Relative mode: [energy] <vpos> <hpos>
		if len(args) == 0 {
			return fmt.Sprintf("%s torpedo mode requires parameters: [energy] <vpos> <hpos>", strings.Title(mode))
		}
		if mode == "relative" {
			// For relative mode, always treat args as offsets, regardless of ICdef
			if len(args) == 2 {
				vpos, err = strconv.Atoi(args[0])
				if err != nil {
					return "Invalid vpos offset. Must be a number."
				}
				hpos, err = strconv.Atoi(args[1])
				if err != nil {
					return "Invalid hpos offset. Must be a number."
				}
			} else if len(args) == 3 {
				energy, err = strconv.Atoi(args[0])
				if err != nil {
					return "Invalid energy amount. Must be a number."
				}
				vpos, err = strconv.Atoi(args[1])
				if err != nil {
					return "Invalid vpos offset. Must be a number."
				}
				hpos, err = strconv.Atoi(args[2])
				if err != nil {
					return "Invalid hpos offset. Must be a number."
				}
			} else {
				return "Invalid syntax for relative mode. Usage: torpedos relative [energy] <vpos> <hpos>"
			}
			// Always treat vpos/hpos as offsets from ship location
			info, ok := i.connections.Load(conn)
			if !ok {
				return "Error: connection not found"
			}
			connInfo := info.(ConnectionInfo)
			var myShip *Object

			for idx := range i.objects {
				obj := i.objects[idx]
				if obj.Type == "Ship" && obj.Name == connInfo.Shipname && obj.Galaxy == connInfo.Galaxy {
					myShip = obj
					break
				}
			}
			if myShip == nil {
				return "Error: unable to determine your ship."
			}
			vpos = myShip.LocationX + vpos
			hpos = myShip.LocationY + hpos

		} else {
			// absolute mode
			if len(args) == 2 {
				vpos, hpos, err = i.parseCoordinates(args[0], args[1], conn, true)
				if err != nil {
					return err.Error()
				}
			} else if len(args) == 3 {
				energy, err = strconv.Atoi(args[0])
				if err != nil {
					return "Invalid energy amount. Must be a number."
				}
				vpos, hpos, err = i.parseCoordinates(args[1], args[2], conn, true)
				if err != nil {
					return err.Error()
				}
			} else {
				return fmt.Sprintf("Invalid syntax for absolute mode. Usage: torpedos absolute [energy] <vpos> <hpos>")
			}
		}
		// Continue with firing logic below
	} else {
		// Simple mode - original torpedoSimple implementation (ie: just vpos/hpos numtorps)
		if len(args) == 2 {
			vpos, err = strconv.Atoi(args[0])
			if err != nil {
				return "Invalid vpos. Must be a number."
			}
			hpos, err = strconv.Atoi(args[1])
			if err != nil {
				return "Invalid hpos. Must be a number."
			}

			energy = 1 // Default energy
		} else if len(args) == 3 {
			energy, err = strconv.Atoi(args[0])
			if err != nil {
				return "Invalid energy amount. Must be a number."
			}
			vpos, hpos, err = i.parseCoordinates(args[1], args[2], conn, false)
			if err != nil {
				return err.Error()
			}
		} else {
			return "Invalid syntax. Usage: torpedos [energy] <vpos> <hpos>"
		}
	}
	// Get connection info for delayPause
	info, ok = i.connections.Load(conn)
	if !ok {
		return "Error: connection not found"
	}
	connInfo := info.(ConnectionInfo)

	// Do a delay

	// --- Firing logic (unchanged) ---
	result := ""
	if energy <= 0 {
		energy = 1
	}
	var myShipIdx int
	var phaobjIdx int
	var myShip *Object
	for idx := range i.objects {
		obj := i.objects[idx]
		if obj.Type == "Ship" && obj.Name == connInfo.Shipname && obj.Galaxy == connInfo.Galaxy {
			myShipIdx = idx
			myShip = obj
			break
		}
	}
	if myShip == nil {
		return "Error: unable to determine your ship."
	}

	// Check if player is targeting their own location
	if vpos == myShip.LocationX && hpos == myShip.LocationY {
		return "ERROR detected by computer!!\r\nYou have attempted to use your present location."
	}

	if i.objects[myShipIdx].TorpedoTubes < numTorps {
		return fmt.Sprintf("Insufficient torpedoes for burst!\n\r%d torpedos left.\n\r", i.objects[myShipIdx].TorpedoTubes)
	}

	// Only allow up to 3 at a time
	if numTorps > 3 || numTorps < 0 {
		return ("Only 3 torpedos allowed per command.")
	}

	// Fire multiple torpedos based on numTorps parameter
	// Removed unused variable hitType
	i.galaxiesMutex.RLock()
	torpSimGal := i.galaxies[connInfo.Galaxy]
	i.galaxiesMutex.RUnlock()
	torpSimRng := newSeededRand()
	if torpSimGal != nil {
		torpSimRng = torpSimGal.rng
	}

	for torpCount := 0; torpCount < numTorps; torpCount++ {
		//start move

		// Add a call to torpedoPathLocked here to get the actual vpos, hpos
		deflection := i.calculateTorpedoDeflection(myShip, torpSimRng)
		actualTargetIdx, objectfound, endX, endY := i.torpedoPathLocked(myShip.LocationX, myShip.LocationY, vpos, hpos, connInfo.Galaxy, deflection)
		if i.objects[myShipIdx].TorpedoTubes < 1 {
			return fmt.Sprintf("Insufficient torpedoes for burst!\n\r%d torpedos left.\n\r", i.objects[myShipIdx].TorpedoTubes)
		}

		// Check if we found a target in the torpedo path
		connInfo = info.(ConnectionInfo)
		outputst := connInfo.OutputState // L, M S
		formt := connInfo.OCdef          // Rel/Abs

		if endX <= 0 {
			endX = 1
		}
		if endX >= MaxSizeX {
			endX = MaxSizeX
		}
		if endY <= 0 {
			endY = 1
		}
		if endY >= MaxSizeY {
			endY = MaxSizeY
		}

		if !objectfound {
			if outputst == "long" {
				if formt == "relative" {
					result = result + fmt.Sprintf("Weapons Officer:  Sir, torpedo %d lost %+d,%+d\n\r", torpCount+1, endX-myShip.LocationX, endY-myShip.LocationY)
				} else {
					if formt == "absolute" {
						result = result + fmt.Sprintf("Weapons Officer:  Sir, torpedo %d lost @%d-%d\n\r", torpCount+1, endX, endY)
					} else {
						result = result + fmt.Sprintf("Weapons Officer:  Sir, torpedo %d lost @%d-%d %+d,%+d\n\r", torpCount+1, endX, endY, endX-myShip.LocationX, endY-myShip.LocationY)
					}
				}
			} else {
				if outputst == "medium" {
					if formt == "relative" {
						result = result + fmt.Sprintf("T%d miss %+d,%+d\n\r", torpCount+1, endX-myShip.LocationX, endY-myShip.LocationY)
					} else {
						if formt == "absolute" {
							result = result + fmt.Sprintf("T%d miss @%d-%d\n\r", torpCount+1, endX, endY)
						} else {
							result = result + fmt.Sprintf("T%d miss @%d-%d %+d,%+d\n\r", torpCount+1, endX, endY, endX-myShip.LocationX, endY-myShip.LocationY)
						}
					}
				} else { //short
					if formt == "relative" {
						result = result + fmt.Sprintf("T%d miss %+d,%+d\n\r", torpCount+1, endX-myShip.LocationX, endY-myShip.LocationY)
					} else {
						if formt == "absolute" {
							result = result + fmt.Sprintf("T%d miss @%d-%d\n\r", torpCount+1, endX, endY)
						} else {
							result = result + fmt.Sprintf("T%d miss @%d-%d %+d,%+d\n\r", torpCount+1, endX, endY, endX-myShip.LocationX, endY-myShip.LocationY)
						}
					}
				}
			}
		}
		// End checking if we found a target in the torpedo path

		// Use the actual target found by torpedoPath or the endpoint coordinates
		var actualVpos, actualHpos int
		if objectfound && actualTargetIdx >= 0 && actualTargetIdx < len(i.objects) {
			phaobjIdx = actualTargetIdx
			actualTarget := i.objects[phaobjIdx]
			actualVpos = actualTarget.LocationX
			actualHpos = actualTarget.LocationY

			// Trying to hit yourself?
			if phaobjIdx == myShipIdx {
				return "ERROR detected by computer!!\r\nYou have attempted to use your present location."
			}
			// Disallow firing at friendly objects
			if i.objects[phaobjIdx].Side == i.objects[myShipIdx].Side {
				locX := i.objects[phaobjIdx].LocationX
				locY := i.objects[phaobjIdx].LocationY
				return fmt.Sprintf("Weapons Officer:  Sir, torpedo 1 neutralized by friendly object @%d-%d", locX, locY)
			}
		} else if objectfound {
			// Index out of bounds, treat as miss
			actualVpos = endX
			actualHpos = endY
		} else {
			// Use the endpoint coordinates when no object is hit
			actualVpos = endX
			actualHpos = endY
		}

		//end move

		// Check if we still have torpedoes
		if i.objects[myShipIdx].TorpedoTubes < 1 {
			break
		}

		// Deduct energy and torpedo from attacker (always happens UNLESS DOCKED)
		// A  torpedo  burst  uses  no  ship  energy.
		if strings.Contains(strings.ToLower(i.objects[myShipIdx].Condition), "docked") {
			i.objects[myShipIdx].Condition = "Docked+Red"
		} else {
			i.objects[myShipIdx].TorpedoTubes = i.objects[myShipIdx].TorpedoTubes - 1
			i.objects[myShipIdx].Condition = "Red"
		}

		if objectfound && phaobjIdx >= 0 && phaobjIdx < len(i.objects) {
			targetObj := i.objects[phaobjIdx]
			if targetObj.LocationX == actualVpos && targetObj.LocationY == actualHpos && targetObj.Galaxy == connInfo.Galaxy {
				// Apply damage for this individual torpedo with independent random rolls
				evt, _ := i.DoDamage("Torpedo", phaobjIdx, myShipIdx, energy*10)

				// Check if star was hit and survived normal damage - 20% chance to destroy it anyway
				targetObj = i.objects[phaobjIdx]
				if targetObj.Type == "Star" && targetObj.TotalShipDamage <= CriticalShipDamage && targetObj.ShipEnergy > 0 {
					if RandomInt(100) < 20 {
						// Force destroy the star
						targetObj.TotalShipDamage = 9999900
						targetObj.ShipEnergy = 0
						targetObj.Condition = "Destroyed"
					}
				}

				// Broadcast combat event to all relevant players
				i.BroadcastCombatEvent(evt, conn)

				// DECWAR: Torpedo hits displace the target in the torpedo's direction of travel.
				// Phaser hits do NOT cause displacement (DECWAR: "if (iwhat .eq. 1) return !phaser hit?")
				targetObj = i.objects[phaobjIdx]
				if isDisplaceable(targetObj.Type) &&
					targetObj.ShipEnergy > 0 && targetObj.TotalShipDamage <= CriticalShipDamage &&
					targetObj.Condition != "Destroyed" {
					// Calculate torpedo direction of travel (from attacker to target), normalized to ±1
					torpDirX := 0
					torpDirY := 0
					tdx := targetObj.LocationX - myShip.LocationX
					tdy := targetObj.LocationY - myShip.LocationY
					if tdx > 0 {
						torpDirX = 1
					} else if tdx < 0 {
						torpDirX = -1
					}
					if tdy > 0 {
						torpDirY = 1
					} else if tdy < 0 {
						torpDirY = -1
					}
					torpDisplaced, destroyedByBH := i.displace(targetObj, torpDirX, torpDirY)
					if torpDisplaced && !destroyedByBH {
						i.broadcastDisplacement(targetObj, false)
					}
					if destroyedByBH {
						// Displaced into black hole — treat as destroyed
						targetObj.Condition = "Destroyed"
						targetObj.ShipEnergy = 0
						i.DestroyObject(targetObj, connInfo.Galaxy)
						if targetObj.Type == "Ship" {
							i.cleanupShipTractorBeams(targetObj)
						}
						// Notify nearby ships about black hole displacement death
						i.broadcastDisplacement(targetObj, true)
						// Notify the destroyed ship and move to pregame
						i.connections.Range(func(key, value interface{}) bool {
							c := key.(net.Conn)
							ci := value.(ConnectionInfo)
							if ci.Shipname == targetObj.Name && ci.Galaxy == targetObj.Galaxy {
								if writerRaw, ok := i.writers.Load(c); ok {
									writer := writerRaw.(*bufio.Writer)
									displayName := targetObj.Name
									if strings.HasPrefix(displayName, "Romulan") {
										displayName = "Romulan"
									}
									i.writeBaudf(c, writer, "%s displaced by blast into BLACK HOLE!\r\n", displayName)
								}
								i.setDestructionCooldownForConn(ci, targetObj.Galaxy)
								ci.Section = "pregame"
								ci.Shipname = ""
								ci.Ship = nil
								ci.Galaxy = 0
								ci.BaudRate = 0
								i.connections.Store(c, ci)
								return false
							}
							return true
						})
						// Remove destroyed object
						i.removeObjectFromSpatialIndex(targetObj)
						removed := false
						for idx := len(i.objects) - 1; idx >= 0; idx-- {
							if i.objects[idx] == targetObj {
								i.removeObjectByIndex(idx)
								removed = true
								break
							}
						}
						if !removed {
							log.Printf("WARNING: Failed to remove destroyed object %s at %d-%d (zombie risk)",
								targetObj.Name, targetObj.LocationX, targetObj.LocationY)
						}
						var dlypse int
						dlypse = calculateDlypse(300, 1, 1, 6, 6)
						var targetConn net.Conn
						i.connections.Range(func(key, value interface{}) bool {
							ci := value.(ConnectionInfo)
							if ci.Shipname == connInfo.Shipname && ci.Galaxy == galaxy {
								targetConn = key.(net.Conn)
								return false
							}
							return true
						})
						destructionMsg := i.delayPause(targetConn, dlypse, galaxy, connInfo.Ship.Type, connInfo.Ship.Side)
						return result + destructionMsg // Always return immediately after removal to avoid stale indices
					}
				}

				// Notify all ships within range if the target was destroyed
				targetObj = i.objects[phaobjIdx]
				if targetObj.TotalShipDamage > CriticalShipDamage || targetObj.ShipEnergy <= 0 {
					// Announce destruction to all ships within DefScanRange
					galaxy := targetObj.Galaxy
					targetName := targetObj.Name
					if strings.HasPrefix(targetName, "Romulan") {
						targetName = "Romulan"
					}
					targetX := targetObj.LocationX
					targetY := targetObj.LocationY

					// Create a snapshot of ships to notify before we modify the objects slice
					var shipsToNotify []*Object
					for _, obj := range i.objects {
						if obj.Type == "Ship" && obj.Galaxy == galaxy && obj.Name != targetName {
							// Check if within range
							if obj.LocationX >= targetX-DefScanRange && obj.LocationX <= targetX+DefScanRange &&
								obj.LocationY >= targetY-DefScanRange && obj.LocationY <= targetY+DefScanRange {
								shipsToNotify = append(shipsToNotify, obj)
							}
						}
					}

					// Now send notifications using the snapshot
					for _, obj := range shipsToNotify {
						// Find the connection for this ship and send the message
						i.connections.Range(func(key, value interface{}) bool {
							c := key.(net.Conn)
							ci := value.(ConnectionInfo)
							if ci.Shipname == obj.Name && ci.Galaxy == obj.Galaxy {
								if writerRaw, ok := i.writers.Load(c); ok {
									writer := writerRaw.(*bufio.Writer)
									var msg string
									if targetObj.Type != "Star" {
										msg = fmt.Sprintf("%s has been destroyed!\r\n", targetName)
									}
									i.writeBaudf(c, writer, "%s", msg)
									// Re-draw the player's prompt
									prompt := i.getPrompt(c)
									if mutexRaw, ok := i.writerMutexs.Load(c); ok {
										mutex := mutexRaw.(*sync.Mutex)
										mutex.Lock()
										writer.WriteString(prompt)
										writer.Flush()
										mutex.Unlock()
									}
								}
								return false // Stop once we find the right connection
							}
							return true
						})
					}

					// Notify the destroyed ship itself
					targetObj := i.objects[phaobjIdx]
					i.connections.Range(func(key, value interface{}) bool {
						c := key.(net.Conn)
						ci := value.(ConnectionInfo)
						if ci.Shipname == targetObj.Name && ci.Galaxy == targetObj.Galaxy {
							if writerRaw, ok := i.writers.Load(c); ok {
								writer := writerRaw.(*bufio.Writer)
								var msg string
								if targetObj.Type == "Star" {
									msg = fmt.Sprintf("Star @%d-%d novas\r\n", targetObj.LocationX, targetObj.LocationY)
								} else {
									destroyedName := targetObj.Name
									if strings.HasPrefix(destroyedName, "Romulan") {
										destroyedName = "Romulan"
									}
									msg = fmt.Sprintf("%s has been destroyed!\r\n", destroyedName)
								}
								i.writeBaudf(c, writer, "%s", msg)
								prompt := i.getPrompt(c)
								if mutexRaw, ok := i.writerMutexs.Load(c); ok {
									mutex := mutexRaw.(*sync.Mutex)
									mutex.Lock()
									writer.WriteString(prompt)
									writer.Flush()
									mutex.Unlock()
								}
							}
							return false // Found and updated
						}
						return true
					})

					// Move player to pregame
					// 1. Find and move the TARGET's connection to pregame
					i.connections.Range(func(key, value interface{}) bool {
						c := key.(net.Conn)
						ci := value.(ConnectionInfo)
						if ci.Shipname == targetObj.Name && ci.Galaxy == targetObj.Galaxy {
							// Set destruction cooldown before resetting connection info
							i.setDestructionCooldownForConn(ci, targetObj.Galaxy)
							ci.Section = "pregame"
							ci.Shipname = ""
							ci.Ship = nil
							ci.Galaxy = 0
							ci.BaudRate = 0
							i.connections.Store(c, ci)
							return false // Found and updated
						}
						return true
					})

					// 2. If its a star, nova
					if targetObj.Type == "Star" {
						i.nova(targetObj, phaobjIdx)
					}

					// 3. Remove the TARGET ship from the galaxy
					i.removeObjectFromSpatialIndex(targetObj)
					// Safely remove the primary target by pointer comparison
					removed := false
					for idx := len(i.objects) - 1; idx >= 0; idx-- {
						if i.objects[idx] == targetObj { // pointer equality
							i.removeObjectByIndex(idx)
							removed = true
							break
						}
					}
					if !removed {
						log.Printf("WARNING: Failed to remove destroyed object %s at %d-%d (zombie risk)",
							targetObj.Name, targetObj.LocationX, targetObj.LocationY)
					}
					// Do delayPause after object removal
					var dlypse int
					dlypse = calculateDlypse(300, 1, 1, 6, 6)
					var targetConn net.Conn
					i.connections.Range(func(key, value interface{}) bool {
						ci := value.(ConnectionInfo)
						if ci.Shipname == connInfo.Shipname && ci.Galaxy == galaxy {
							targetConn = key.(net.Conn)
							return false
						}
						return true
					})
					destructionMsg := i.delayPause(targetConn, dlypse, galaxy, connInfo.Ship.Type, connInfo.Ship.Side)
					return result + destructionMsg
				}
			} else {
				// Target moved or was destroyed, but torpedo was still fired and consumed
			} // End of if-else for objectfound
		} else {
			// Miss - torpedo was fired and consumed but hit nothing
		}
	}
	// Do delayPause after torpedoes are shot
	var dlypse int
	dlypse = calculateDlypse(300, 1, 1, 6, 6)
	var targetConn net.Conn
	i.connections.Range(func(key, value interface{}) bool {
		ci := value.(ConnectionInfo)
		if ci.Shipname == connInfo.Shipname && ci.Galaxy == galaxy {
			targetConn = key.(net.Conn)
			return false
		}
		return true
	})
	destructionMsg := i.delayPause(targetConn, dlypse, galaxy, connInfo.Ship.Type, connInfo.Ship.Side)
	return result + destructionMsg
}

// nova is triggered when a star is destroyed or hit by a nova
func (i *Interpreter) nova(targetObj *Object, attackerIdx int) {
	if targetObj.Type != "Star" {
		return // Should not happen, but safety
	}

	galaxy := targetObj.Galaxy

	// Adjacent offsets (8 directions)
	adjacentOffsets := [][2]int{
		{1, 0}, {-1, 0}, {0, 1}, {0, -1},
		{1, 1}, {1, -1}, {-1, 1}, {-1, -1},
	}

	// --- PHASE 1: BFS to discover all connected stars (no removals yet) ---
	type pos struct {
		x, y int
	}
	queue := []pos{{targetObj.LocationX, targetObj.LocationY}}
	log.Printf("Starting nova BFS with initial position: (%d, %d)", targetObj.LocationX, targetObj.LocationY)
	visited := make(map[pos]bool)
	visited[pos{targetObj.LocationX, targetObj.LocationY}] = true

	var starPositions []pos
	starPositions = append(starPositions, pos{targetObj.LocationX, targetObj.LocationY})

	for len(queue) > 0 {
		current := queue[0]
		queue = queue[1:]

		for _, offset := range adjacentOffsets {
			nx := current.x + offset[0]
			ny := current.y + offset[1]

			isValid, _, _ := i.validateGalaxyBoundaries(galaxy, nx, ny)
			if !isValid {
				log.Printf("Skipping invalid position: (%d, %d)", nx, ny)
				continue
			}

			p := pos{nx, ny}
			if visited[p] {
				log.Printf("Already visited position: (%d, %d)", nx, ny)
				continue
			}

			adjObj := i.getObjectAtLocation(galaxy, nx, ny)
			if adjObj != nil && adjObj.Type == "Star" {
				visited[p] = true
				queue = append(queue, p)
				starPositions = append(starPositions, p)
			}
		}
	}

	// --- PHASE 2: Process all discovered stars ---
	// Optional: dedup non-star damage (prevents over-damage from multi-adjacent stars)
	processedNonStars := make(map[*Object]bool)
	// Track objects destroyed by this nova for safe removal in PHASE 3
	var novaDestroyedObjects []*Object

	for _, p := range starPositions {
		starObj := i.getObjectAtLocation(galaxy, p.x, p.y)
		if starObj == nil {
			continue // Rare race, but safe
		}

		// Broadcast nova message for this star (matches old recursive logic)
		galaxy := starObj.Galaxy
		novaX := starObj.LocationX
		novaY := starObj.LocationY
		for idx := range i.objects {
			notifyObj := i.objects[idx]
			if notifyObj.Type == "Ship" && notifyObj.Galaxy == galaxy &&
				notifyObj.LocationX >= novaX-DefScanRange && notifyObj.LocationX <= novaX+DefScanRange &&
				notifyObj.LocationY >= novaY-DefScanRange && notifyObj.LocationY <= novaY+DefScanRange {
				i.connections.Range(func(key, value interface{}) bool {
					c := key.(net.Conn)
					ci := value.(ConnectionInfo)
					if ci.Shipname == notifyObj.Name && ci.Galaxy == notifyObj.Galaxy {
						if writerRaw, ok := i.writers.Load(c); ok {
							writer := writerRaw.(*bufio.Writer)
							msg := fmt.Sprintf("Star @%d-%d novas\r\n", novaX, novaY)
							i.writeBaudf(c, writer, "%s", msg)
							// Re-draw prompt
							prompt := i.getPrompt(c)
							if mutexRaw, ok := i.writerMutexs.Load(c); ok {
								mutex := mutexRaw.(*sync.Mutex)
								mutex.Lock()
								writer.WriteString(prompt)
								writer.Flush()
								mutex.Unlock()
							}
						}
						return false
					}
					return true
				})
			}
		}

		// Remove from spatial index now (safe, discovery complete)
		i.removeObjectFromSpatialIndex(starObj)

		// Apply nova effects to all adjacent non-star objects
		for _, offset := range adjacentOffsets {
			nx := p.x + offset[0]
			ny := p.y + offset[1]

			isValid, _, _ := i.validateGalaxyBoundaries(galaxy, nx, ny)
			if !isValid {
				continue
			}

			adjObj := i.getObjectAtLocation(galaxy, nx, ny)
			if adjObj == nil || adjObj.Type == "Star" || processedNonStars[adjObj] {
				continue
			}

			// Optional: mark to dedup (remove this and the map if you want cumulative damage)
			processedNonStars[adjObj] = true

			// Reuse your existing applyNovaDamage logic
			heavy, halve := false, false
			switch adjObj.Type {
			case "Ship", "Base":
				heavy = true
			case "Romulan":
				heavy, halve = true, true
			case "Planet":
				// planet-specific
			case "Black Hole":
				// black holes take light nova damage
			}
			i.applyNovaDamage(adjObj, heavy, halve)

			// Check if object was destroyed by nova (same threshold as torpedoSimple)
			novaDestroyed := (adjObj.Type == "Ship" || adjObj.Type == "Base" || adjObj.Type == "Romulan") &&
				(adjObj.ShipEnergy <= 0 || adjObj.TotalShipDamage > CriticalShipDamage || adjObj.Condition == "Destroyed")

			if novaDestroyed {
				adjObj.Condition = "Destroyed"
				adjObj.ShipEnergy = 0
				i.DestroyObject(adjObj, galaxy)

				// Clean up tractor beams for destroyed ships
				if adjObj.Type == "Ship" {
					i.cleanupShipTractorBeams(adjObj)
				}
			}

			// --- Broadcast nova collateral damage to nearby ships ---
			// For each ship, calculate relative coordinates for both star and damaged object

			// Broadcast to all ships within normal scan range of the *damaged object*
			targetX := adjObj.LocationX
			targetY := adjObj.LocationY

			ships := i.getObjectsByType(galaxy, "Ship")
			if ships != nil {
				for _, ship := range ships {
					dx := AbsInt(ship.LocationX - targetX)
					dy := AbsInt(ship.LocationY - targetY)
					if max(dx, dy) <= (DefScanRange / 2) {
						// Find the player's connection and send the message
						i.connections.Range(func(key, value interface{}) bool {
							c := key.(net.Conn)
							ci := value.(ConnectionInfo)
							if ci.Shipname == ship.Name && ci.Galaxy == galaxy && ci.Section == "gowars" {
								if writerRaw, ok := i.writers.Load(c); ok {
									writer := writerRaw.(*bufio.Writer)
									starRelX := p.x - ship.LocationX
									starRelY := p.y - ship.LocationY
									objRelX := adjObj.LocationX - ship.LocationX
									objRelY := adjObj.LocationY - ship.LocationY
									relMsg := fmt.Sprintf("Star @%d-%d %+d,%+d makes hit on %s @%d-%d %+d,%+d\r\n",
										p.x, p.y, starRelX, starRelY, strings.Title(adjObj.Name), adjObj.LocationX, adjObj.LocationY, objRelX, objRelY)
									i.writeBaudf(c, writer, "\r\n%s\r\n", relMsg)

									// Re-draw the prompt
									prompt := i.getPrompt(c)
									if mutexRaw, ok := i.writerMutexs.Load(c); ok {
										mutex := mutexRaw.(*sync.Mutex)
										mutex.Lock()
										writer.WriteString(prompt)
										writer.Flush()
										mutex.Unlock()
									}
								}
								return false // stop ranging once found
							}
							return true
						})
					}
				}
			}
			// --- END

			if !novaDestroyed {
				adjObj.Condition = "Red"
			}

			// Handle displacement (ships/bases/romulans/planets/black holes) - only if not destroyed
			// DECWAR: displacement direction is away from the exploding star (object - star)
			if isDisplaceable(adjObj.Type) &&
				adjObj.ShipEnergy > 0 && adjObj.Condition != "Destroyed" {
				dirX := adjObj.LocationX - p.x
				dirY := adjObj.LocationY - p.y
				displaced, destroyedByBH := i.displace(adjObj, dirX, dirY)
				if displaced && !destroyedByBH {
					i.broadcastDisplacement(adjObj, false)
				}
				if destroyedByBH {
					// Object was displaced into a black hole and destroyed
					adjObj.Condition = "Destroyed"
					adjObj.ShipEnergy = 0
					i.DestroyObject(adjObj, galaxy)
					if adjObj.Type == "Ship" {
						i.cleanupShipTractorBeams(adjObj)
					}
					// Mark as nova-destroyed so PHASE 3 cleans it up
					if !novaDestroyed {
						novaDestroyed = true
						// Move player to pregame for black hole death
						if adjObj.Type == "Ship" {
							i.connections.Range(func(key, value interface{}) bool {
								c := key.(net.Conn)
								ci := value.(ConnectionInfo)
								if ci.Shipname == adjObj.Name && ci.Galaxy == galaxy {
									if writerRaw, ok := i.writers.Load(c); ok {
										writer := writerRaw.(*bufio.Writer)
										displayName := adjObj.Name
										if strings.HasPrefix(displayName, "Romulan") {
											displayName = "Romulan"
										}
										i.writeBaudf(c, writer, "%s displaced by blast into BLACK HOLE!\r\n", displayName)
									}
									i.setDestructionCooldownForConn(ci, galaxy)
									ci.Section = "pregame"
									ci.Shipname = ""
									ci.Ship = nil
									ci.Galaxy = 0
									ci.BaudRate = 0
									i.connections.Store(c, ci)
									return false
								}
								return true
							})
						}
						i.removeObjectFromSpatialIndex(adjObj)
						novaDestroyedObjects = append(novaDestroyedObjects, adjObj)
					}
					i.broadcastDisplacement(adjObj, true)
				}
			}

			// Handle destruction: move destroyed ship players to pregame, set cooldown, remove object
			if novaDestroyed {
				if adjObj.Type == "Ship" {
					// Find the destroyed ship's connection and move to pregame
					i.connections.Range(func(key, value interface{}) bool {
						c := key.(net.Conn)
						ci := value.(ConnectionInfo)
						if ci.Shipname == adjObj.Name && ci.Galaxy == galaxy {
							// Notify the destroyed player
							if writerRaw, ok := i.writers.Load(c); ok {
								writer := writerRaw.(*bufio.Writer)
								novaDestroyedName := adjObj.Name
								if strings.HasPrefix(novaDestroyedName, "Romulan") {
									novaDestroyedName = "Romulan"
								}
								i.writeBaudf(c, writer, "%s has been destroyed!\r\n", novaDestroyedName)
							}
							// Set destruction cooldown before resetting connection info
							i.setDestructionCooldownForConn(ci, galaxy)
							ci.Section = "pregame"
							ci.Shipname = ""
							ci.Ship = nil
							ci.Galaxy = 0
							ci.BaudRate = 0
							i.connections.Store(c, ci)
							return false
						}
						return true
					})
				}
				// Remove destroyed object from spatial index and track for removal in phase 3
				i.removeObjectFromSpatialIndex(adjObj)
				novaDestroyedObjects = append(novaDestroyedObjects, adjObj)
			}
		}
	}

	// --- PHASE 3: Final cleanup - remove all exploded stars and nova-destroyed objects from objects slice ---
	// First remove objects destroyed by this nova (use pointer set for safety, iterate backwards)
	for idx := len(i.objects) - 1; idx >= 0; idx-- {
		obj := i.objects[idx]
		for _, destroyed := range novaDestroyedObjects {
			if obj == destroyed {
				i.removeObjectByIndex(idx)
				break
			}
		}
	}

	// Then remove all exploded stars
	for _, p := range starPositions {
		for idx := len(i.objects) - 1; idx >= 0; idx-- {
			obj := i.objects[idx]
			if obj.Galaxy == galaxy && obj.LocationX == p.x && obj.LocationY == p.y && obj.Type == "Star" {
				if idx < 0 || idx >= len(i.objects) {
					log.Printf("Attempted to remove object at invalid index: %d (objects length: %d)", idx, len(i.objects))
					continue
				}
				i.removeObjectByIndex(idx)
				break
			}
		}
	}

	// Rebuild indexes after all changes
	log.Printf("Rebuilding spatial indexes after nova processing")
	i.rebuildSpatialIndexes()
}

// findNearbyEmptySector finds a nearby empty sector for displacement.
// It searches in an expanding square around (x, y) up to a radius of 3.
func (i *Interpreter) findNearbyEmptySector(galaxy uint16, x, y int) (int, int) {
	// Only check adjacent sectors (±1)
	for dx := -1; dx <= 1; dx++ {
		for dy := -1; dy <= 1; dy++ {
			nx, ny := x+dx, y+dy
			isValid, _, _ := i.validateGalaxyBoundaries(galaxy, nx, ny)
			if !isValid {
				continue
			}
			if dx == 0 && dy == 0 {
				continue
			}
			if i.getObjectAtLocation(galaxy, nx, ny) == nil {
				return nx, ny
			}
		}
	}
	// If no empty sector found, return original location
	return x, y
}

// displace displaces an object in a specific direction, matching DECWAR's JUMP subroutine.
// dirX, dirY specify the displacement direction (typically -1, 0, or 1 for each axis).
// The object is moved exactly one sector in that direction if:
//   - The new position is within galaxy boundaries
//   - The new position is empty
//
// If the new position contains a black hole, the object is destroyed.
// If the new position is out of bounds or occupied (non-black-hole), no displacement occurs.
// Returns (displaced, destroyedByBlackHole).
// isDisplaceable returns true if the given object type can be displaced by torpedoes and nova blasts.
func isDisplaceable(objType string) bool {
	return objType == "Ship" || objType == "Romulan" || objType == "Base" || objType == "Planet" || objType == "Black Hole"
}

func (i *Interpreter) displace(obj *Object, dirX, dirY int) (bool, bool) {
	galaxy := obj.Galaxy
	x, y := obj.LocationX, obj.LocationY

	// Normalize direction to at most ±1 per axis (matching DECWAR's single-sector displacement)
	if dirX > 1 {
		dirX = 1
	} else if dirX < -1 {
		dirX = -1
	}
	if dirY > 1 {
		dirY = 1
	} else if dirY < -1 {
		dirY = -1
	}

	// No direction means no displacement
	if dirX == 0 && dirY == 0 {
		return false, false
	}

	newX := x + dirX
	newY := y + dirY

	// Check if new position is within galaxy boundaries
	isValid, _, _ := i.validateGalaxyBoundaries(galaxy, newX, newY)
	if !isValid {
		return false, false
	}

	// Check what's at the new location
	occupant := i.getObjectAtLocation(galaxy, newX, newY)

	// If there's a black hole at the new position, the object is destroyed
	if occupant != nil && occupant.Type == "Black Hole" {
		// Remove object from its old location (DECWAR: call setdsp(iloc1, jloc1, 0))
		i.removeObjectFromSpatialIndex(obj)
		// Mark as destroyed
		obj.Condition = "Destroyed"
		obj.ShipEnergy = 0
		obj.TotalShipDamage = CriticalShipDamage + 1
		return true, true
	}

	// If new position is occupied by anything else, no displacement
	if occupant != nil {
		return false, false
	}

	// New position is empty — displace the object there
	i.updateObjectLocation(obj, newX, newY)

	// Set condition to Red and undock (matching DECWAR: shpcon(j,KSPCON) = RED; docked(j) = .FALSE.)
	if obj.Type == "Ship" {
		obj.Condition = "Red"
	}

	return true, false
}

// broadcastDisplacement sends a displacement message to all ships within range of
// the displaced object. Message format follows DECWAR's OUTHIT routine:
//   - Long absolute:  "<name> displaced to @<X>-<Y>, <shields>%"
//   - Long relative:  "<name> displaced to <+dx>,<+dy>, <shields>%"
//   - Long both:      "<name> displaced to @<X>-<Y> <+dx>,<+dy>, <shields>%"
//   - Medium absolute: "<name> --@<X>-<Y>, <shields>%"
//   - Medium relative: "<name> --<+dx>,<+dy>, <shields>%"
//   - Medium both:     "<name> --@<X>-<Y> <+dx>,<+dy>, <shields>%"
//   - Short absolute:  "<name> >@<X>-<Y>"
//   - Short relative:  "<name> ><+dx>,<+dy>"
//   - Short both:      "<name> >@<X>-<Y> <+dx>,<+dy>"
//
// For black hole displacement deaths use destroyedByBlackHole=true:
//   - Long:  "<name> displaced by blast into BLACK HOLE!"
//   - Medium: "<name> -> BH!"
//   - Short:  "<name> -> BH"
func (i *Interpreter) broadcastDisplacement(obj *Object, destroyedByBlackHole bool) {
	galaxy := obj.Galaxy
	ships := i.getObjectsByType(galaxy, "Ship")
	if ships == nil {
		return
	}

	shieldPct := float64(obj.Shields) / float64(InitialShieldValue) * 100.0
	objName := strings.Title(obj.Name)
	if obj.Side == "romulan" {
		objName = "Romulan"
	} else if obj.Type == "Base" {
		objName = strings.Title(obj.Side) + " Base"
	} else if obj.Type == "Planet" {
		objName = strings.Title(obj.Side) + " Planet"
	} else if obj.Type == "Black Hole" {
		objName = "Black Hole"
	}

	for _, ship := range ships {
		if ship.Name == obj.Name {
			continue
		}
		dx := AbsInt(ship.LocationX - obj.LocationX)
		dy := AbsInt(ship.LocationY - obj.LocationY)
		if max(dx, dy) > DefScanRange {
			continue
		}

		i.connections.Range(func(key, value interface{}) bool {
			c := key.(net.Conn)
			ci := value.(ConnectionInfo)
			if ci.Galaxy != galaxy || ci.Shipname != ship.Name || ci.Section != "gowars" {
				return true
			}
			if ci.Ship != nil && !ci.Ship.RadioOnOff {
				return true
			}

			outputState := ci.OutputState
			ocdef := ci.OCdef

			var msg string
			if destroyedByBlackHole {
				switch outputState {
				case "long":
					msg = fmt.Sprintf("%s displaced by blast into BLACK HOLE!\r\n", objName)
				case "medium":
					msg = fmt.Sprintf("%s -> BH!\r\n", objName)
				default:
					msg = fmt.Sprintf("%s -> BH\r\n", objName)
				}
			} else {
				relX := obj.LocationX - ship.LocationX
				relY := obj.LocationY - ship.LocationY

				var locPart string
				switch ocdef {
				case "relative":
					locPart = fmt.Sprintf("%+d,%+d", relX, relY)
				case "absolute":
					locPart = fmt.Sprintf("@%d-%d", obj.LocationX, obj.LocationY)
				default: // "both" or unset
					locPart = fmt.Sprintf("@%d-%d %+d,%+d", obj.LocationX, obj.LocationY, relX, relY)
				}

				switch outputState {
				case "long":
					msg = fmt.Sprintf("%s displaced to %s, %s%.1f%%\r\n", objName, locPart, boolToSign(obj.ShieldsUpDown), shieldPct)
				case "medium":
					msg = fmt.Sprintf("%s --%s, %s%.1f%%\r\n", objName, locPart, boolToSign(obj.ShieldsUpDown), shieldPct)
				default:
					msg = fmt.Sprintf("%s >%s\r\n", objName, locPart)
				}
			}

			if writerRaw, ok := i.writers.Load(c); ok {
				writer := writerRaw.(*bufio.Writer)
				i.writeBaudf(c, writer, "%s", msg)

				prompt := i.getPrompt(c)
				if mutexRaw, ok := i.writerMutexs.Load(c); ok {
					mutex := mutexRaw.(*sync.Mutex)
					mutex.Lock()
					writer.WriteString(prompt)
					writer.Flush()
					mutex.Unlock()
				}
			}
			return false
		})
	}

	// Notify the displaced ship itself (only for non-black-hole displacements;
	// black hole deaths are already handled by the callers).
	if !destroyedByBlackHole && obj.Type == "Ship" {
		i.connections.Range(func(key, value interface{}) bool {
			c := key.(net.Conn)
			ci := value.(ConnectionInfo)
			if ci.Galaxy != galaxy || ci.Shipname != obj.Name || ci.Section != "gowars" {
				return true
			}

			outputState := ci.OutputState

			// For the displaced ship itself, always use absolute coordinates
			// (relative would be 0,0 which is meaningless).
			locPart := fmt.Sprintf("@%d-%d", obj.LocationX, obj.LocationY)

			var msg string
			switch outputState {
			case "long":
				msg = fmt.Sprintf("Displaced to %s, %s%.1f%%\r\n", locPart, boolToSign(obj.ShieldsUpDown), shieldPct)
			case "medium":
				msg = fmt.Sprintf("Displaced --%s, %s%.1f%%\r\n", locPart, boolToSign(obj.ShieldsUpDown), shieldPct)
			default:
				msg = fmt.Sprintf("Displaced >%s\r\n", locPart)
			}

			if writerRaw, ok := i.writers.Load(c); ok {
				writer := writerRaw.(*bufio.Writer)
				i.writeBaudf(c, writer, "%s", msg)

				prompt := i.getPrompt(c)
				if mutexRaw, ok := i.writerMutexs.Load(c); ok {
					mutex := mutexRaw.(*sync.Mutex)
					mutex.Lock()
					writer.WriteString(prompt)
					writer.Flush()
					mutex.Unlock()
				}
			}
			return false
		})
	}
}

// hasEnemyInstallations checks if a planet has enemy bases or ships present.
func (i *Interpreter) hasEnemyInstallations(planet *Object) bool {
	galaxy := planet.Galaxy
	x, y := planet.LocationX, planet.LocationY
	planetSide := planet.Side

	// Check for enemy bases or ships at the same location
	for _, obj := range i.objects {
		if obj.Galaxy == galaxy && obj.LocationX == x && obj.LocationY == y {
			if (obj.Type == "Base" || obj.Type == "Ship") && obj.Side != "" && obj.Side != planetSide {
				return true
			}
		}
	}
	return false
}

// applyNovaDamage applies nova damage to an object.
// If heavy is true, damage is high. If halve is true, energy damage is halved (for Romulans).
func (i *Interpreter) applyNovaDamage(obj *Object, heavy bool, halve bool) {
	// Example damage values; adjust as needed for your game balance
	baseDamage := 1200 + RandomInt(800)
	if !heavy {
		baseDamage = 600 + RandomInt(400)
	}
	if halve {
		baseDamage = baseDamage / 2
	}

	// Apply to shields first if present
	if obj.Shields > 0 {
		shieldDamage := baseDamage
		obj.ShieldsDamage += shieldDamage
		obj.Shields -= shieldDamage
		if obj.Shields < 0 {
			obj.Shields = 0
		}
	}

	// Apply to ship energy or total damage
	if obj.Type == "Ship" || obj.Type == "Base" || obj.Type == "Romulan" {
		obj.ShipEnergy -= baseDamage
		obj.TotalShipDamage += baseDamage * 100 // Scale to 100x for consistent TotalShipDamage scale
		if obj.ShipEnergy < 0 {
			obj.ShipEnergy = 0
		}
	} else if obj.Type == "Planet" || obj.Type == "Black Hole" {
		// Planets and black holes: apply energy damage and increment total damage
		obj.ShipEnergy -= baseDamage
		obj.TotalShipDamage += baseDamage * 100
		if obj.ShipEnergy < 0 {
			obj.ShipEnergy = 0
		}
	} else if obj.Type == "Star" {
		obj.TotalShipDamage += baseDamage * 100
	}
	// NOTE: Displacement after nova is handled by the caller (nova function) which knows the
	// blast direction. DECWAR's NOVA subroutine calls JUMP with the direction from the star
	// to the object. We don't displace here to avoid double-displacement.
}

// phaserSimple handles all phaser targeting modes with mode parameter
func (i *Interpreter) phaserSimple(mode string, args []string, conn net.Conn) string {
	energy := 200 // Default energy
	var vpos, hpos int
	var err error

	info, ok := i.connections.Load(conn)
	if !ok {
		return "Error: connection not found"
	}
	connInfo := info.(ConnectionInfo)

	var attacker *Object
	var target *Object

	// --- Acquire attacker and target pointers ---
	attacker = i.getShipByName(connInfo.Galaxy, connInfo.Shipname)
	if attacker == nil {
		return "Error: unable to determine your ship."
	}

	if mode == "computed" {
		shipname := ""
		if len(args) == 1 {
			shipname = args[0]
		} else if len(args) == 2 {
			energy, err = strconv.Atoi(args[0])
			if err != nil {
				return "Invalid energy amount. Must be a number."
			}
			shipname = args[1]
		} else {
			return "Invalid syntax for computed mode. Usage: phasers computed [energy] <shipname>"
		}

		// Validate energy range: 50-500 units per spec
		if energy < 50 || energy > 500 {
			return "Weapons Officer:  Energy must be between 50 and 500 units, sir."
		}

		// Modified computed targeting: only consider ships within MaxRange in the same galaxy,
		// prefer the closest one (smallest Chebyshev distance). If none, report out of range.
		abbr := strings.ToLower(shipname)
		ships := i.getObjectsByType(connInfo.Galaxy, "Ship")
		bestDist := MaxRange + 1
		for _, obj := range ships {
			if obj == attacker {
				continue
			}
			if strings.HasPrefix(strings.ToLower(obj.Name), abbr) {
				dx := AbsInt(obj.LocationX - attacker.LocationX)
				dy := AbsInt(obj.LocationY - attacker.LocationY)
				dist := dx
				if dy > dx {
					dist = dy
				}
				if dist <= MaxRange && dist < bestDist {
					target = obj
					bestDist = dist
				}
			}
		}
		if target == nil {
			return "Target out of range."
		}
	} else {
		if len(args) == 2 {
			vpos, hpos, err = i.parseCoordinates(args[0], args[1], conn, mode == "absolute")
		} else if len(args) == 3 {
			energy, err = strconv.Atoi(args[0])
			if err != nil {
				return "Invalid energy amount. Must be a number."
			}
			vpos, hpos, err = i.parseCoordinates(args[1], args[2], conn, mode == "absolute")
		} else {
			return "Invalid syntax for phaser command."
		}

		// Validate energy range: 50-500 units per spec
		if energy < 50 || energy > 500 {
			return "Weapons Officer:  Energy must be between 50 and 500 units, sir."
		}
		if err != nil {
			return err.Error()
		}

		if mode == "relative" {
			vpos += attacker.LocationX
			hpos += attacker.LocationY
		}

		target = i.getObjectAtLocation(connInfo.Galaxy, vpos, hpos)

		if target == nil {
			return "No object at those coordinates, sir."
		}
	}

	if target == attacker {
		return "ERROR detected by computer!!\r\nYou have attempted to use your present location."
	}

	var dlypse int
	dlypse = calculateDlypse(300, 1, 1, 6, 6)

	// --- Now acquire Lock for mutation ---
	var evt *CombatEvent
	var attackErr error
	var destroyed bool
	var targetName string
	var targetConn net.Conn

	evt, attackErr = i.phaserAttack(attacker, target, energy)
	if attackErr == nil && evt.Message == "destroyed" {
		destroyed = true
		targetName = target.Name
		if strings.HasPrefix(targetName, "Romulan") {
			targetName = "Romulan"
		}
		targetConn = i.getShipConnection(*target)
		// Remove the object from the game
		for idx := range i.objects {
			if i.objects[idx] == target {
				i.removeObjectByIndex(idx)
				break
			}
		}
	}

	if attackErr != nil {
		return attackErr.Error()
	}

	i.BroadcastCombatEvent(evt, conn)

	// Do all output and connection updates after releasing the lock

	// Do all output and connection updates after releasing the lock
	if destroyed && targetConn != nil {
		if writerRaw, ok := i.writers.Load(targetConn); ok {
			writer := writerRaw.(*bufio.Writer)
			var msg string
			if target.Type == "Star" {
				msg = fmt.Sprintf("Star @%d-%d novas\r\n", target.LocationX, target.LocationY)
			} else {
				msg = fmt.Sprintf("%s has been destroyed!\r\n", targetName)
			}
			i.writeBaudf(targetConn, writer, "%s", msg)
		}

		if targetConnInfo, ok := i.connections.Load(targetConn); ok {
			ci := targetConnInfo.(ConnectionInfo)
			// Set destruction cooldown before resetting connection info
			i.setDestructionCooldownForConn(ci, connInfo.Galaxy)
			ci.Section = "pregame"
			ci.Shipname = ""
			ci.Ship = nil
			ci.Galaxy = 0
			ci.BaudRate = 0
			i.connections.Store(targetConn, ci)
		}
	}
	destructionMsg := i.delayPause(targetConn, dlypse, connInfo.Galaxy, connInfo.Ship.Type, connInfo.Ship.Side)

	// Check if attacker was destroyed during the delay (e.g., by return fire from
	// a base or robot). If energy hit 0, properly destroy the ship and move to pregame.
	if attacker.ShipEnergy <= 0 {
		// Send message to the attacking ship
		if writerRaw, ok := i.writers.Load(conn); ok {
			writer := writerRaw.(*bufio.Writer)
			i.writeBaudf(conn, writer, "%s", "SHIELDS USE UP LAST OF ENERGY!\r\n")
		}

		// Notify everyone within range
		galaxy := attacker.Galaxy
		attackerName := attacker.Name
		for idx := range i.objects {
			obj := i.objects[idx]
			if obj.Type == "Ship" && obj.Galaxy == galaxy &&
				(obj.LocationX >= attacker.LocationX-(DefScanRange/2) && obj.LocationX <= attacker.LocationX+(DefScanRange/2)) &&
				(obj.LocationY >= attacker.LocationY-(DefScanRange/2) && obj.LocationY <= attacker.LocationY+(DefScanRange/2)) {
				i.connections.Range(func(key, value interface{}) bool {
					c := key.(net.Conn)
					ci := value.(ConnectionInfo)
					if ci.Shipname == obj.Name && ci.Galaxy == obj.Galaxy {
						if writerRaw, ok := i.writers.Load(c); ok {
							writer := writerRaw.(*bufio.Writer)
							msg := fmt.Sprintf("%s  RUNS OUT OF ENERGY!!\r\n", attackerName)
							i.writeBaudf(c, writer, "%s", msg)
						}
						return false // Only send once per ship
					}
					return true
				})
			}
		}

		// Destroy the attacker ship: mark destroyed, move connection to pregame,
		// and remove from the game world
		attacker.Condition = "Destroyed"
		i.DestroyObject(attacker, galaxy)

		// Move attacker's connection to pregame
		if connInfoUpdate, ok := i.connections.Load(conn); ok {
			ci := connInfoUpdate.(ConnectionInfo)
			i.setDestructionCooldownForConn(ci, galaxy)
			ci.Section = "pregame"
			ci.Shipname = ""
			ci.Ship = nil
			ci.Galaxy = 0
			ci.BaudRate = 0
			i.connections.Store(conn, ci)
		}

		// Remove the attacker object from the game
		for idx := len(i.objects) - 1; idx >= 0; idx-- {
			if i.objects[idx] == attacker {
				i.removeObjectByIndex(idx)
				break
			}
		}
	}

	return "Phasers fired.\n\r" + destructionMsg
}

func (i *Interpreter) getTargetOutputState(target *Object) (string, string) {
	var outputState, ocdef string // Defaults: "" (handle in caller)
	i.connections.Range(func(key, value interface{}) bool {
		connInfo := value.(ConnectionInfo)
		if connInfo.Shipname == target.Name && connInfo.Galaxy == target.Galaxy {
			outputState = connInfo.OutputState
			ocdef = connInfo.OCdef
			return false // Stop
		}
		return true
	})
	return outputState, ocdef
}

// Announce phaser hits to anyone within range
func (i *Interpreter) AnnounceMsg(energy, vpos, hpos int, conn net.Conn, targetIdx, attackerIdx, shieldDamage, energyDamage, ihitaValue int, hitType string, disp bool) {
	// Get attacker and target objects
	attacker := i.objects[attackerIdx]
	target := i.objects[targetIdx]

	// Get connection info
	if info, ok := i.connections.Load(conn); ok {
		connInfo := info.(ConnectionInfo)
		galaxy := connInfo.Galaxy

		// Find all ships within range of the target
		for idx := range i.objects {
			obj := i.objects[idx]

			if obj.Type == "Ship" && obj.Galaxy == galaxy &&
				(obj.LocationX >= target.LocationX-(DefScanRange/2) && obj.LocationX <= target.LocationX+(DefScanRange/2)) &&
				(obj.LocationY >= target.LocationY-(DefScanRange/2) && obj.LocationY <= target.LocationY+(DefScanRange/2)) {

				// Get output settings for this ship
				outputState, ocdef := i.getTargetOutputState(obj)

				// Calculate relative position from observer ship to target
				relativeX := target.LocationX - obj.LocationX
				relativeY := target.LocationY - obj.LocationY

				// Calculate relative position from observer ship to attacker
				attackerRelativeX := attacker.LocationX - obj.LocationX
				attackerRelativeY := attacker.LocationY - obj.LocationY

				// Calculate shield percentages
				var attackerShieldPct float64
				if attacker.Shields > 0 {
					attackerShieldPct = (float64(attacker.Shields) / float64(InitialShieldValue)) * 100.0
				}

				var targetShieldPct float64
				targetShieldPct = float64(target.Shields) / float64(InitialShieldValue) * 100.0

				// Create damage result
				damageResult := DamageResult{
					Damage:    ihitaValue,
					Deflected: disp,
				}

				// Determine weapon type
				var weaponType WeaponType
				if hitType == "Phaser" {
					weaponType = WeaponPhaser
				} else {
					if hitType == "Torpedo" {
						weaponType = WeaponTorpedo
					} else {
						weaponType = WeaponNova
					}
				}

				// Create message data
				messageData := CombatMessageData{
					Attacker:          attacker,
					Target:            target,
					DamageResult:      damageResult,
					WeaponType:        weaponType,
					BlastAmount:       energy,
					RelativeX:         relativeX,
					RelativeY:         relativeY,
					AttackerRelativeX: attackerRelativeX,
					AttackerRelativeY: attackerRelativeY,
					OutputState:       outputState,
					OCdef:             ocdef,
					AttackerShields:   attackerShieldPct,
					TargetShields:     targetShieldPct,
					Displaced:         disp,
				}

				// Format message
				formatter := &MessageFormatter{}
				message := formatter.FormatCombatMessage(messageData)

				// Find the connection for this ship and send the message
				i.connections.Range(func(key, value interface{}) bool {
					c := key.(net.Conn)
					ci := value.(ConnectionInfo)

					if ci.Shipname == obj.Name && ci.Galaxy == obj.Galaxy && ci.Shipname != attacker.Name {
						// Only send if the receiving ship's radio is ON
						if ci.Ship != nil && !ci.Ship.RadioOnOff {
							return false // Skip if radio is off
						}
						if writerRaw, ok := i.writers.Load(c); ok {
							writer := writerRaw.(*bufio.Writer)
							i.writeBaudf(c, writer, "%s", message)

							// Re-draw the player's prompt
							prompt := i.getPrompt(c)
							if mutexRaw, ok := i.writerMutexs.Load(c); ok {
								mutex := mutexRaw.(*sync.Mutex)
								mutex.Lock()
								writer.WriteString(prompt)
								writer.Flush()
								mutex.Unlock()
							}
						}
						return false // Stop once we find the right connection
					}
					return true
				})
			}
		}
	}
}

// HitMsg sends phaser/torpedo hit message to the attacker
func (i *Interpreter) HitMsg(energy, vpos, hpos int, conn net.Conn, targetIdx, attackerIdx, shieldDamage, energyDamage, ihitaValue int, hitType string, disp bool) {
	// Get connection info
	if info, ok := i.connections.Load(conn); ok {
		connInfo := info.(ConnectionInfo)

		// Get attacker and target objects
		attacker := i.objects[attackerIdx]
		target := i.objects[targetIdx]

		// Calculate shield percentages
		var attackerShieldPct float64
		if attacker.Shields > 0 {
			attackerShieldPct = (float64(attacker.Shields) / float64(InitialShieldValue)) * 100.0
		}

		var targetShieldPct float64
		targetShieldPct = float64(target.Shields) / float64(InitialShieldValue) * 100.0

		// Calculate relative position
		relativeX := target.LocationX - attacker.LocationX
		relativeY := target.LocationY - attacker.LocationY

		// For HitMsg, attacker is the observer, so attacker relative is always 0,0
		attackerRelativeX := 0
		attackerRelativeY := 0

		// Create damage result
		damageResult := DamageResult{
			Damage:    ihitaValue,
			Deflected: disp,
		}

		// Determine weapon type
		var weaponType WeaponType
		if hitType == "Phaser" {
			weaponType = WeaponPhaser
		} else {
			if hitType == "Torpedo" {
				weaponType = WeaponTorpedo
			} else {
				weaponType = WeaponNova
			}
		}

		// Create message data
		messageData := CombatMessageData{
			Attacker:          attacker,
			Target:            target,
			DamageResult:      damageResult,
			WeaponType:        weaponType,
			BlastAmount:       energy,
			RelativeX:         relativeX,
			RelativeY:         relativeY,
			AttackerRelativeX: attackerRelativeX,
			AttackerRelativeY: attackerRelativeY,
			OutputState:       connInfo.OutputState,
			OCdef:             connInfo.OCdef,
			AttackerShields:   attackerShieldPct,
			TargetShields:     targetShieldPct,
			Displaced:         disp,
		}

		// Format and send message to attacker
		formatter := &MessageFormatter{}
		message := formatter.FormatCombatMessage(messageData)

		if writerRaw, ok := i.writers.Load(conn); ok {
			writer := writerRaw.(*bufio.Writer)
			i.writeBaudf(conn, writer, "%s", message)
		}

		// Announce to everyone nearby
		i.AnnounceMsg(energy, vpos, hpos, conn, targetIdx, attackerIdx, shieldDamage, energyDamage, ihitaValue, hitType, disp)
	}
}

// broadcastRomulanTaunt sends a Romulan taunt message to specified targets
// Updated to support system wide messages
func (i *Interpreter) broadcastRomulanTaunt(senderName, target, message string, galaxy uint16) {

	// Format the message with sender name
	var formattedMessage string
	if senderName == "SYSTEM" {
		formattedMessage = fmt.Sprintf("\r\n%s\r\n", message)
	} else {
		if strings.HasPrefix(senderName, "Romulan") {
			senderName = "Romulan"
		}
		formattedMessage = fmt.Sprintf("\r\nmessage from %s: %s\r\n", senderName, message)
	}

	// Broadcast to connections based on target type
	i.connections.Range(func(key, value interface{}) bool {
		conn := key.(net.Conn)
		connInfo := value.(ConnectionInfo)

		// Skip if not in the right galaxy
		if connInfo.Galaxy != galaxy {
			return true
		}

		// Skip if not in gowars mode (taunts are only for active players)
		if connInfo.Section != "gowars" {
			return true
		}

		// Check radio status - skip if radio is off
		shouldSend := false
		if connInfo.Ship != nil {
			// Access ship data directly from connection info to avoid deadlock
			// The connection info should have up-to-date ship data
			radioOn := connInfo.Ship.RadioOnOff
			shipSide := connInfo.Ship.Side
			shipName := connInfo.Ship.Name

			if !radioOn {
				return true // Skip ships with radio off
			}

			// Determine if this connection should receive the taunt
			switch target {
			case "all":
				shouldSend = true
			case "federation":
				shouldSend = (shipSide == "federation")
			case "empire":
				shouldSend = (shipSide == "empire")
			default:
				// Specific ship name
				shouldSend = (shipName == target)
			}
		}

		if shouldSend {
			if writerRaw, ok := i.writers.Load(conn); ok {
				writer := writerRaw.(*bufio.Writer)
				if mutexRaw, ok := i.writerMutexs.Load(conn); ok {
					mutex := mutexRaw.(*sync.Mutex)
					mutex.Lock()
					writer.WriteString(formattedMessage)
					writer.Flush()
					mutex.Unlock()
				}
			}
		}

		return true
	})
}
