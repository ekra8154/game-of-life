// Core Game of Life Logic and UI Controls (adapted for PixiJS integration)

// Global variables from previous version (some will be used by PixiJS setup)
let baseCellSize = 10;
let cols, rows; // These will define the logical grid size
let grid; // The 2D array representing cell states
let running = false; // Start paused by default
let gameSpeed = 200; // Milliseconds between updates
let lastUpdateTime = 0;

// Zoom and Pan variables (will be applied to PixiJS container/viewport)
let zoomLevel = 2.55; // Start at zoom level corresponding to 50% on the display scale
const minZoom = 0.1;
const maxZoom = 5.0;
let viewOffsetX = 0; // Renamed from offsetX to avoid conflict with Pixi properties if any
let viewOffsetY = 0; // Renamed from offsetY
let isPanning = false;
let lastPanX = 0, lastPanY = 0;

let showGridLines = true; // We'll decide how to implement this with PixiJS
let currentGenerationHue = 1; // Start hue at 1 (1-360 range for alive cells)
const HUE_INCREMENT = 2;     // Reduced from 10 for slower, smoother color changes

// UI Element References (assuming IDs remain the same from new index.html)
const speedSlider = document.getElementById('speedSlider');
const pausePlayButton = document.getElementById('pausePlayButton');
const gridLinesCheckbox = document.getElementById('gridLinesCheckbox');
const randomizeButton = document.getElementById('randomizeButton');
const clearButton = document.getElementById('clearButton');
const zoomLevelDisplay = document.getElementById('zoomLevelDisplay'); // Get the new element
const trailSlider = document.getElementById('trailSlider'); // Get trail slider
const shapeSelect = document.getElementById('shapeSelect'); // Get shape dropdown
const addShapeButton = document.getElementById('addShapeButton'); // Get new button
const toolSelect = document.getElementById('toolSelect'); // Get tool dropdown
const sizeSlider = document.getElementById('sizeSlider'); // Get size slider
const sizeDisplay = document.getElementById('sizeDisplay'); // Get size display span
let zoomDisplayTimeout = null; // Timeout ID for hiding the display

// Tool state
let currentTool = 'brush'; // 'brush', 'eraser', 'shape'
let brushSize = 1; // 1 to max value of size slider

// Shape Definitions (Remove single and block)
const shapes = {
    'glider': [
        [0, 0, 1],
        [1, 0, 1],
        [0, 1, 1]
    ],
    'beehive': [
        [0, 1, 1, 0],
        [1, 0, 0, 1],
        [0, 1, 1, 0]
    ],
    'blinker': [
        [1, 1, 1]
    ],
    'toad': [
        [0, 1, 1, 1],
        [1, 1, 1, 0]
    ],
    'lwss': [ 
        [0, 1, 1, 1, 1],
        [1, 0, 0, 0, 1],
        [0, 0, 0, 0, 1],
        [1, 0, 0, 1, 0] 
    ],
    'gosper_glider_gun': [
      [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0],
      [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0],
      [0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,1,1],
      [0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,1,1],
      [1,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
      [1,1,0,0,0,0,0,0,0,0,1,0,0,0,1,0,1,1,0,0,0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0],
      [0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0],
      [0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
      [0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] 
    ],
    'small_bomb': [
        [1, 1, 1, 0, 1, 1, 1],
        [1, 0, 1, 0, 1, 0, 1],
        [1, 1, 1, 0, 1, 1, 1]
    ],
    'eater1': [
        [1, 1, 0, 0],
        [1, 0, 1, 0],
        [0, 0, 1, 0],
        [0, 0, 1, 1]
    ]
};

let selectedShapeName = 'glider'; // Default shape (first in list now)
let currentOrientationIndex = 0; 
let currentShapeOrientations = []; 
let currentPattern; 
let lastMouseEvent = null; 

let isDragging = false; // For brush/eraser/shape dragging
let lastModifiedCell = { i: -1, j: -1 }; // Renamed from lastPlacedCell

// --- PixiJS specific variables will be declared here ---
let app; // The Pixi Application
let gameContainer; // SINGLE main container for ALL game elements
let gridLinesGraphics; 
let cellGraphicsForRender; // Temp graphics for rendering current cells TO texture
let worldBorderGraphics; 

let trailRenderTexture;    // RenderTexture sized to the WORLD
let trailSprite;           // Sprite added to gameContainer to display the texture
let TRAIL_FADE_ALPHA = 0.20; // Default trail fade alpha set lower (matches slider value=20)
let fadeRectangleGraphics; // For fading the world-sized render texture

// Hover Preview
let hoverPreviewGraphics; 
let lastHoveredCell = { i: -1, j: -1 };

// --- Game Logic Functions (mostly unchanged) ---
function createGrid(c, r) {
    let arr = new Array(c);
    for (let i = 0; i < c; i++) {
        arr[i] = new Array(r);
        for (let j = 0; j < r; j++) {
            arr[i][j] = 0;
        }
    }
    return arr;
}

function randomizeGrid(currentGrid) {
    for (let i = 0; i < cols; i++) {
        for (let j = 0; j < rows; j++) {
            currentGrid[i][j] = (Math.random() > 0.7) ? currentGenerationHue : 0;
        }
    }
    if (!running) {
        app.renderer.render(gameContainer, {renderTexture: trailRenderTexture, clear: true});
    }
    updateCellGraphicsForRender(); // Update cell graphics content
    app.renderer.render(cellGraphicsForRender, {renderTexture: trailRenderTexture, clear: true}); // Render directly to texture, clearing previous state
}

function clearGrid() {
    for (let i = 0; i < cols; i++) {
        for (let j = 0; j < rows; j++) {
            grid[i][j] = 0;
        }
    }
    if (!running) {
        app.renderer.render(gameContainer, {renderTexture: trailRenderTexture, clear: true});
    }
    updateCellGraphicsForRender(); // Update cell graphics content
    app.renderer.render(cellGraphicsForRender, {renderTexture: trailRenderTexture, clear: true}); // Render directly to texture, clearing previous state
}

function updateGameLogic() { // Renamed from update() to avoid conflict with Pixi's ticker.update
    let nextGrid = createGrid(cols, rows);
    for (let i = 0; i < cols; i++) {
        for (let j = 0; j < rows; j++) {
            let state = grid[i][j]; 
            let neighbors = countNeighbors(grid, i, j);
            if (state === 0 && neighbors === 3) {
                nextGrid[i][j] = currentGenerationHue; 
            } else if (state !== 0 && (neighbors === 2 || neighbors === 3)) {
                nextGrid[i][j] = state; 
            } else {
                nextGrid[i][j] = 0; 
            }
        }
    }
    grid = nextGrid;
    
    // Increment hue for the NEXT generation, ensuring it stays in 1-360 range
    currentGenerationHue = (currentGenerationHue - 1 + HUE_INCREMENT) % 360 + 1;
}

function countNeighbors(currentGrid, x, y) {
    let sum = 0;
    for (let i = -1; i < 2; i++) {
        for (let j = -1; j < 2; j++) {
            if (i === 0 && j === 0) continue;
            let col = (x + i + cols) % cols;
            let row = (y + j + rows) % rows;
            if (currentGrid[col][row] !== 0) { // Count any non-dead cell as a neighbor
                sum++;
            }
        }
    }
    return sum;
}

// --- UI Interaction Functions (mostly unchanged, but draw() calls will be Pixi draws) ---
if (speedSlider) {
    speedSlider.value = (parseInt(speedSlider.max) + parseInt(speedSlider.min)) - gameSpeed;
    speedSlider.addEventListener('input', (event) => {
        gameSpeed = (parseInt(speedSlider.max) + parseInt(speedSlider.min)) - parseInt(event.target.value);
    });
}

function updatePausePlayButtonText() {
    if (pausePlayButton) {
        pausePlayButton.textContent = running ? 'Pause' : 'Play';
    }
}

function togglePausePlay() {
    running = !running;
    if (running) {
        lastUpdateTime = performance.now(); // Set/reset lastUpdateTime only when starting/resuming
    }
    updatePausePlayButtonText();
}

if (pausePlayButton) {
    pausePlayButton.addEventListener('click', togglePausePlay);
}

if (gridLinesCheckbox) {
    gridLinesCheckbox.checked = showGridLines;
    gridLinesCheckbox.addEventListener('change', (event) => {
        showGridLines = event.target.checked;
        // draw(); // PixiJS will redraw
    });
}

if (randomizeButton) {
    randomizeButton.addEventListener('click', () => {
        randomizeGrid(grid);
        // draw(); // PixiJS will redraw
    });
}

if (clearButton) {
    clearButton.addEventListener('click', () => {
        clearGrid();
        // draw(); // PixiJS will redraw
    });
}

// --- Setup Trail Slider --- 
if (trailSlider) {
    // Set initial slider position based on the default alpha
    trailSlider.value = TRAIL_FADE_ALPHA * 100; 

    trailSlider.addEventListener('input', (event) => {
        // Convert slider value (0-98) to alpha (0.00-0.98)
        TRAIL_FADE_ALPHA = parseInt(event.target.value) / 100.0;
    });
}

// --- Setup Tool Selector --- 
if (toolSelect) {
    currentTool = toolSelect.value;
    toolSelect.addEventListener('change', (event) => {
        currentTool = event.target.value;
        // Update hover preview immediately based on new tool
        const currentCell = lastMouseEvent ? getCellFromScreenEvent(lastMouseEvent) : null;
        updateHoverPreview(currentCell);
    });
}

// --- Setup Size Slider --- 
if (sizeSlider && sizeDisplay) {
    brushSize = parseInt(sizeSlider.value);
    sizeDisplay.textContent = brushSize;
    sizeSlider.addEventListener('input', (event) => {
        brushSize = parseInt(event.target.value);
        sizeDisplay.textContent = brushSize;
        // Update hover preview immediately if tool is brush or eraser
        if (currentTool === 'brush' || currentTool === 'eraser') {
             const currentCell = lastMouseEvent ? getCellFromScreenEvent(lastMouseEvent) : null;
             updateHoverPreview(currentCell);
        }
    });
}

// --- Setup Shape Selector --- 
if (shapeSelect) {
    selectedShapeName = shapeSelect.value; // Initialize with the first available shape
    // Pre-calculate initial orientations
    let basePattern = shapes[selectedShapeName] || [[1]]; // Fallback to single pixel if somehow empty
    currentShapeOrientations = [basePattern];
    currentShapeOrientations.push(rotatePattern(currentShapeOrientations[0])); // 90 deg
    currentShapeOrientations.push(rotatePattern(currentShapeOrientations[1])); // 180 deg
    currentShapeOrientations.push(rotatePattern(currentShapeOrientations[2])); // 270 deg
    currentOrientationIndex = 0;
    currentPattern = currentShapeOrientations[currentOrientationIndex];

    shapeSelect.addEventListener('change', (event) => {
        selectedShapeName = event.target.value;
        basePattern = shapes[selectedShapeName] || [[1]];
        // Recalculate orientations for the new shape
        currentShapeOrientations = [basePattern];
        currentShapeOrientations.push(rotatePattern(currentShapeOrientations[0])); 
        currentShapeOrientations.push(rotatePattern(currentShapeOrientations[1])); 
        currentShapeOrientations.push(rotatePattern(currentShapeOrientations[2])); 
        currentOrientationIndex = 0; // Reset orientation
        currentPattern = currentShapeOrientations[currentOrientationIndex];
        
        const currentCell = lastMouseEvent ? getCellFromScreenEvent(lastMouseEvent) : null;
        updateHoverPreview(currentCell);
    });
}

// --- Setup Add Shape Button --- 
if (addShapeButton) {
    addShapeButton.addEventListener('click', () => {
        captureAndAddShape();
    });
}

// --- Function to capture, name, and add the current pattern --- 
function captureAndAddShape() {
    let liveCells = [];
    let minRow = rows, maxRow = -1, minCol = cols, maxCol = -1;

    // 1. Find all live cells and their bounding box
    for (let r = 0; r < rows; r++) {
        for (let c = 0; c < cols; c++) {
            if (grid[c][r] !== 0) { // Found a live cell
                liveCells.push({ c, r });
                minCol = Math.min(minCol, c);
                maxCol = Math.max(maxCol, c);
                minRow = Math.min(minRow, r);
                maxRow = Math.max(maxRow, r);
            }
        }
    }

    // 2. Handle case with no live cells
    if (liveCells.length === 0) {
        alert("No live cells found to save as a shape.");
        return;
    }

    // 3. Calculate pattern dimensions and create array
    const patternWidth = maxCol - minCol + 1;
    const patternHeight = maxRow - minRow + 1;
    let newPattern = Array(patternHeight).fill(0).map(() => Array(patternWidth).fill(0));

    // 4. Populate the pattern array (using 1 for live)
    for (const cell of liveCells) {
        const relCol = cell.c - minCol;
        const relRow = cell.r - minRow;
        newPattern[relRow][relCol] = 1;
    }

    // 5. Get a name for the shape
    const shapeName = prompt("Enter a name for the new shape:", "MyShape");

    // 6. Validate the name
    if (!shapeName) { // User cancelled or entered empty string
        return;
    }
    if (shapes[shapeName]) {
        alert(`Shape name "${shapeName}" already exists. Please choose another.`);
        return;
    }

    // 7. Add shape to shapes object
    shapes[shapeName] = newPattern;

    // 8. Add shape to dropdown menu
    const newOption = document.createElement('option');
    newOption.value = shapeName;
    newOption.textContent = shapeName;
    if (shapeSelect) {
        shapeSelect.appendChild(newOption);
        // Optionally select the new shape
        shapeSelect.value = shapeName;
        // Manually trigger the logic that normally happens on 'change'
        selectedShapeName = shapeName;
        let basePattern = shapes[selectedShapeName];
        currentShapeOrientations = [basePattern];
        currentShapeOrientations.push(rotatePattern(currentShapeOrientations[0])); 
        currentShapeOrientations.push(rotatePattern(currentShapeOrientations[1])); 
        currentShapeOrientations.push(rotatePattern(currentShapeOrientations[2])); 
        currentOrientationIndex = 0;
        currentPattern = currentShapeOrientations[currentOrientationIndex];
        const currentCell = lastMouseEvent ? getCellFromScreenEvent(lastMouseEvent) : null;
        updateHoverPreview(currentCell);
    }

    alert(`Shape "${shapeName}" added!`);
}

// --- Main Setup and Game Loop (to be heavily modified for PixiJS) ---

function setupPixi() {
    // Initialize Pixi Application
    app = new PIXI.Application({
        width: window.innerWidth,
        height: window.innerHeight,
        backgroundColor: 0x111111, // Dark background similar to original CSS
        antialias: true,
        resolution: window.devicePixelRatio || 1,
        autoDensity: true,
    });
    document.body.appendChild(app.view); // app.view is the PixiJS canvas element

    // SINGLE Game Container - added to stage
    gameContainer = new PIXI.Container();
    app.stage.addChild(gameContainer);
    
    // Calculate initial logical grid size (same as before)
    let visibleColsBasedOnWindow = Math.floor(window.innerWidth / baseCellSize);
    let visibleRowsBasedOnWindow = Math.floor(window.innerHeight / baseCellSize);
    cols = visibleColsBasedOnWindow * 2; 
    rows = visibleRowsBasedOnWindow * 2;
    grid = createGrid(cols, rows); 

    const worldPixelWidth = cols * baseCellSize;
    const worldPixelHeight = rows * baseCellSize;

    // Create RenderTexture sized to the game WORLD
    trailRenderTexture = PIXI.RenderTexture.create({
        width: worldPixelWidth,
        height: worldPixelHeight,
        resolution: 1 // Use resolution 1 for world-space texture
    });

    // Create a sprite for the trails and add it INSIDE gameContainer
    trailSprite = new PIXI.Sprite(trailRenderTexture);
    gameContainer.addChild(trailSprite); // Drawn first within container

    // Graphics for drawing CURRENT cells (rendered to texture)
    cellGraphicsForRender = new PIXI.Graphics();

    // Graphics for grid lines (added to gameContainer, drawn over trails)
    gridLinesGraphics = new PIXI.Graphics();
    gameContainer.addChild(gridLinesGraphics);
    
    // Graphics for world border (added to gameContainer, drawn over trails/grid)
    worldBorderGraphics = new PIXI.Graphics();
    gameContainer.addChild(worldBorderGraphics);

    // Graphics for Hover Preview (added last to gameContainer to draw on top)
    hoverPreviewGraphics = new PIXI.Graphics();
    gameContainer.addChild(hoverPreviewGraphics);

    // Graphics for fading the world-sized render texture
    fadeRectangleGraphics = new PIXI.Graphics();

    // Calculate initial viewOffset to center the world
    const initialZoomLevel = 2.55; // Keep the desired starting zoom
    zoomLevel = initialZoomLevel;
    const viewportWorldWidth = app.screen.width / zoomLevel;
    const viewportWorldHeight = app.screen.height / zoomLevel;
    viewOffsetX = (worldPixelWidth - viewportWorldWidth) / 2;
    viewOffsetY = (worldPixelHeight - viewportWorldHeight) / 2;
    viewOffsetX = Math.max(0, Math.min(viewOffsetX, worldPixelWidth - viewportWorldWidth));
    viewOffsetY = Math.max(0, Math.min(viewOffsetY, worldPixelHeight - viewportWorldHeight));

    updatePausePlayButtonText();
    app.ticker.add(pixiGameLoop);
    if (running) { 
        lastUpdateTime = performance.now();
    }
    
    // Initial draw calls
    app.renderer.render(new PIXI.Graphics().beginFill(0x111111).drawRect(0,0,worldPixelWidth, worldPixelHeight).endFill(), {renderTexture: trailRenderTexture, clear: true}); // Clear world RT
    updateCellGraphicsForRender(); // Draw initial empty cell state
    app.renderer.render(cellGraphicsForRender, {renderTexture: trailRenderTexture, clear: false}); // Draw initial cells to RT
    updateStaticGraphics(); // Initial draw of grid/border
    updateGameContainerTransform(); // Apply initial pan/zoom
}

function pixiGameLoop(delta) {
    let gameLogicUpdated = false;

    if (running) {
        const currentTime = performance.now();
        const deltaTimeUpdate = currentTime - lastUpdateTime;
        if (deltaTimeUpdate > gameSpeed) {
            // 1. Fade the world-sized trailRenderTexture
            fadeRectangleGraphics.clear();
            const fadeAmount = 1.0 - TRAIL_FADE_ALPHA;
            fadeRectangleGraphics.beginFill(0x111111, fadeAmount); // Use background color for fade
            fadeRectangleGraphics.drawRect(0, 0, trailRenderTexture.width, trailRenderTexture.height);
            fadeRectangleGraphics.endFill();
            app.renderer.render(fadeRectangleGraphics, { renderTexture: trailRenderTexture, clear: false });

            updateGameLogic(); // 2. Update the game state
            lastUpdateTime = currentTime - (deltaTimeUpdate % gameSpeed);
            gameLogicUpdated = true;
        }
    }

    // 3. Update cell graphics buffer and render cells to their texture if logic updated
    if (gameLogicUpdated) { 
         updateCellGraphicsForRender(); 
         app.renderer.render(cellGraphicsForRender, { renderTexture: trailRenderTexture, clear: false }); // Draw current cells over faded trails
    }
    
    // 4. Update static graphics (grid/border) always (as they depend on zoom for line thickness)
    updateStaticGraphics();
    
    // 5. Update the main game container's transform for pan/zoom always
    updateGameContainerTransform();
}

// Renamed from updateCellGraphics
function updateCellGraphicsForRender() { 
    cellGraphicsForRender.clear();
    const currentCellSize = baseCellSize; 
    cellGraphicsForRender.filters = []; 
    for (let i = 0; i < cols; i++) {
        for (let j = 0; j < rows; j++) {
            if (grid[i][j] !== 0) { 
                const cellHueFromGrid = grid[i][j]; 
                const hexColor = hslToHex(cellHueFromGrid - 1, 100, 50); 
                cellGraphicsForRender.beginFill(hexColor);
                // Draw into the world-space texture coordinates
                cellGraphicsForRender.drawRect(i * currentCellSize, j * currentCellSize, currentCellSize, currentCellSize);
                cellGraphicsForRender.endFill();
            }
        }
    }
}

// Renamed from drawStaticElements
function updateStaticGraphics() { 
    const currentCellSize = baseCellSize; 

    gridLinesGraphics.clear();
    if (showGridLines) {
        gridLinesGraphics.visible = true;
        const targetScreenGridThickness = Math.min(1.0, Math.max(0.1, zoomLevel * 0.75));
        gridLinesGraphics.lineStyle(targetScreenGridThickness / zoomLevel, 0x444444, 1);
        for (let i = 0; i <= cols; i++) { 
            gridLinesGraphics.moveTo(i * currentCellSize, 0);
            gridLinesGraphics.lineTo(i * currentCellSize, rows * currentCellSize);
        }
        for (let j = 0; j <= rows; j++) { 
            gridLinesGraphics.moveTo(0, j * currentCellSize);
            gridLinesGraphics.lineTo(cols * currentCellSize, j * currentCellSize);
        }
    } else {
        gridLinesGraphics.visible = false;
    }

    worldBorderGraphics.clear();
    worldBorderGraphics.lineStyle(1.5 / zoomLevel, 0x555555, 1);
    worldBorderGraphics.drawRect(0, 0, cols * currentCellSize, rows * currentCellSize);
}

// New function to handle gameContainer transform
function updateGameContainerTransform() {
    gameContainer.x = -viewOffsetX * zoomLevel;
    gameContainer.y = -viewOffsetY * zoomLevel;
    gameContainer.scale.set(zoomLevel);
}

// --- Event Listeners for Pan, Zoom, Click (adapted for PixiJS canvas) ---

function getCellFromScreenEvent(event) {
    const localPos = gameContainer.toLocal(new PIXI.Point(event.clientX, event.clientY));

    const i = Math.floor(localPos.x / baseCellSize);
    const j = Math.floor(localPos.y / baseCellSize);

    if (i >= 0 && i < cols && j >= 0 && j < rows) {
        return { i, j };
    }
    return null;
}

function addPixiEventListeners() {
    app.view.addEventListener('wheel', (event) => {
        event.preventDefault();
        
        const pointBeforeZoom = gameContainer.toLocal(new PIXI.Point(event.clientX, event.clientY));

        const oldZoom = zoomLevel;
        const zoomFactor = event.deltaY > 0 ? 0.9 : 1.1;
        zoomLevel = Math.max(minZoom, Math.min(zoomLevel * zoomFactor, maxZoom));

        if (oldZoom !== zoomLevel) {
            const mouseScreenX = event.clientX - app.view.getBoundingClientRect().left;
            const mouseScreenY = event.clientY - app.view.getBoundingClientRect().top;

            const worldMouseX = viewOffsetX + mouseScreenX / oldZoom;
            const worldMouseY = viewOffsetY + mouseScreenY / oldZoom;

            viewOffsetX = worldMouseX - mouseScreenX / zoomLevel;
            viewOffsetY = worldMouseY - mouseScreenY / zoomLevel;

            // Update and show zoom level display
            if (zoomLevelDisplay) {
                clearTimeout(zoomDisplayTimeout);
                const percent = ((zoomLevel - minZoom) / (maxZoom - minZoom)) * 100;
                zoomLevelDisplay.textContent = `Zoom: ${percent.toFixed(0)}%`;
                zoomLevelDisplay.style.display = 'block';
                requestAnimationFrame(() => { // Ensure display:block is applied before opacity transition
                    zoomLevelDisplay.style.opacity = '1';
                });

                zoomDisplayTimeout = setTimeout(() => {
                    zoomLevelDisplay.style.opacity = '0';
                    // Wait for opacity transition to finish before setting display:none
                    setTimeout(() => { zoomLevelDisplay.style.display = 'none'; }, 300); 
                }, 1500);
            }
        }
    });

    app.view.addEventListener('contextmenu', (event) => event.preventDefault());

    app.view.addEventListener('mousedown', (event) => {
        if (event.button === 2) { // Panning
            isPanning = true;
            lastPanX = event.clientX;
            lastPanY = event.clientY;
        } else if (event.button === 0) { // Left-click for current tool
            isDragging = true; 
            const cell = getCellFromScreenEvent(event);
            if (cell) {
                applyTool(cell.i, cell.j, currentTool, brushSize, currentPattern);
                lastModifiedCell = { i: cell.i, j: cell.j }; 
            }
        }
    });

    window.addEventListener('mousemove', (event) => {
        lastMouseEvent = event; 
        if (isPanning) {
            const dx = event.clientX - lastPanX;
            const dy = event.clientY - lastPanY;
            viewOffsetX -= dx / zoomLevel;
            viewOffsetY -= dy / zoomLevel;
            lastPanX = event.clientX;
            lastPanY = event.clientY;
            // Transform is updated in the game loop
            return; // Don't do hover or drag logic while panning
        } 
        
        if (isDragging) { 
            const currentCell = getCellFromScreenEvent(event);
            if (currentCell && (currentCell.i !== lastModifiedCell.i || currentCell.j !== lastModifiedCell.j)) {
                applyTool(currentCell.i, currentCell.j, currentTool, brushSize, currentPattern);
                lastModifiedCell = { i: currentCell.i, j: currentCell.j };
                updateHoverPreview(currentCell); // Keep hover updated while dragging
            }
            return; 
        }
        
        const currentHoverCell = getCellFromScreenEvent(event);
        updateHoverPreview(currentHoverCell);
        
    });
    
    app.view.addEventListener('mouseleave', () => {
        if (lastHoveredCell.i !== -1 || lastHoveredCell.j !== -1) { 
             hoverPreviewGraphics.clear();
             lastHoveredCell = { i: -1, j: -1 };
        }
    });
    
    window.addEventListener('mouseup', (event) => {
        if (event.button === 2) {
             isPanning = false;
        } else if (event.button === 0) { 
            isDragging = false; 
            lastModifiedCell = { i: -1, j: -1 }; 
        }
    });

    document.addEventListener('keydown', (event) => {
        if (event.code === 'Space') {
            event.preventDefault();
            togglePausePlay();
        }
        if ((event.key === 'r' || event.key === 'R') && currentTool === 'shape') { // Only rotate if shape tool active
            event.preventDefault(); 
            if (currentShapeOrientations.length > 0) {
                 currentOrientationIndex = (currentOrientationIndex + 1) % currentShapeOrientations.length;
                 currentPattern = currentShapeOrientations[currentOrientationIndex];
                 const currentCell = lastMouseEvent ? getCellFromScreenEvent(lastMouseEvent) : null;
                 updateHoverPreview(currentCell);
            }
        }
    });
}

// Initial setup call
window.onload = () => {
    setupPixi();
    addPixiEventListeners();
};

// Helper function to convert HSL to Hex color for PixiJS
function hslToHex(h_zero_based, s, l) { // ensure h is 0-359 for this function
    s /= 100;
    l /= 100;
    const k = n => (n + h_zero_based / 30) % 12;
    const a = s * Math.min(l, 1 - l);
    const f = n =>
        l - a * Math.max(-1, Math.min(k(n) - 3, Math.min(9 - k(n), 1)));
    const r = Math.round(255 * f(0));
    const g = Math.round(255 * f(8));
    const b = Math.round(255 * f(4));
    return (r << 16) + (g << 8) + b;
}

window.addEventListener('resize', () => {
    app.renderer.resize(window.innerWidth, window.innerHeight);
    // Resize the world-sized render texture? No, its size is fixed.
    // The view into it changes via gameContainer transform.
    // However, the fadeRectangleGraphics should adjust if needed, but it uses app.screen
    // We might need to recalculate initial centering offsets if desired.
});

// New function to handle drawing the hover preview
function updateHoverPreview(currentCell) {
    hoverPreviewGraphics.clear();
    lastHoveredCell = { i: -1, j: -1 }; 

    if (currentCell) { 
        const previewColor = 0xFFFFFF; 
        const previewAlpha = 0.4;     
        hoverPreviewGraphics.beginFill(previewColor, previewAlpha);

        if (currentTool === 'brush' || currentTool === 'eraser') {
            const size = brushSize;
            const halfSizeFloor = Math.floor((size - 1) / 2);
            const halfSizeCeil = Math.ceil((size - 1) / 2);
            // Draw a square preview centered at the current cell
            const startX = (currentCell.i - halfSizeFloor) * baseCellSize;
            const startY = (currentCell.j - halfSizeFloor) * baseCellSize;
            const previewWidth = size * baseCellSize;
            const previewHeight = size * baseCellSize;
            hoverPreviewGraphics.drawRect(startX, startY, previewWidth, previewHeight);
        } else if (currentTool === 'shape' && currentPattern) {
            const pattern = currentPattern;
            const patternHeight = pattern.length;
            const patternWidth = pattern[0].length;
            for (let dy = 0; dy < patternHeight; dy++) {
                for (let dx = 0; dx < patternWidth; dx++) {
                    if (pattern[dy][dx] === 1) {
                        const drawX = (currentCell.i + dx) * baseCellSize;
                        const drawY = (currentCell.j + dy) * baseCellSize;
                        hoverPreviewGraphics.drawRect(drawX, drawY, baseCellSize, baseCellSize);
                    }
                }
            }
        } 
        hoverPreviewGraphics.endFill();
        lastHoveredCell = { i: currentCell.i, j: currentCell.j };
    }
}

// --- Helper function to rotate a 2D pattern array 90 degrees clockwise ---
function rotatePattern(pattern) {
    if (!pattern || pattern.length === 0) return [];
    const oldHeight = pattern.length;
    const oldWidth = pattern[0].length;
    const newHeight = oldWidth;
    const newWidth = oldHeight;
    
    // Create new grid initialized to 0
    let newPattern = Array(newHeight).fill(0).map(() => Array(newWidth).fill(0));

    for (let r = 0; r < oldHeight; r++) {
        for (let c = 0; c < oldWidth; c++) {
            newPattern[c][newWidth - 1 - r] = pattern[r][c];
        }
    }
    return newPattern;
}

// NEW function to apply the selected tool
function applyTool(centerX, centerY, tool, size, pattern) {
    let cellsChanged = false;
    const halfSizeFloor = Math.floor((size - 1) / 2);
    const halfSizeCeil = Math.ceil((size - 1) / 2);

    if (tool === 'brush' || tool === 'eraser') {
        for (let dx = -halfSizeFloor; dx <= halfSizeCeil; dx++) {
            for (let dy = -halfSizeFloor; dy <= halfSizeCeil; dy++) {
                const targetCol = (centerX + dx + cols) % cols;
                const targetRow = (centerY + dy + rows) % rows;
                const newValue = (tool === 'brush') ? currentGenerationHue : 0;
                if (grid[targetCol][targetRow] !== newValue) {
                    grid[targetCol][targetRow] = newValue;
                    cellsChanged = true;
                }
            }
        }
    } else if (tool === 'shape' && pattern) {
        const patternHeight = pattern.length;
        const patternWidth = pattern[0].length;
        for (let dy = 0; dy < patternHeight; dy++) {
            for (let dx = 0; dx < patternWidth; dx++) {
                if (pattern[dy][dx] === 1) {
                    const targetCol = (centerX + dx + cols) % cols;
                    const targetRow = (centerY + dy + rows) % rows;
                    if (grid[targetCol][targetRow] === 0) {
                        cellsChanged = true;
                    }
                    grid[targetCol][targetRow] = currentGenerationHue;
                }
            }
        }
    }

    // If paused and changes occurred, trigger immediate redraw of cell texture
    if (!running && cellsChanged) {
        updateCellGraphicsForRender();
        app.renderer.render(cellGraphicsForRender, {renderTexture: trailRenderTexture, clear: true});
    }
} 