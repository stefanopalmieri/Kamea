// cayley-table.js — Interactive 16x16 Cayley table component

export class CayleyTable {
    constructor(container) {
        this.container = container;
        this.data = null;
        this.cells = [];       // [row][col] → td elements
        this.rowHeaders = [];  // [row] → th elements
        this.colHeaders = [];  // [col] → th elements
        this.hlRow = -1;
        this.hlCol = -1;
        this.onCellClick = null;
    }

    build(data) {
        this.data = data;
        this.container.innerHTML = '';
        this.cells = [];
        this.rowHeaders = [];
        this.colHeaders = [];

        const table = document.createElement('table');
        table.className = 'cayley-table';

        // Header row
        const thead = document.createElement('thead');
        const headerRow = document.createElement('tr');
        const corner = document.createElement('th');
        corner.textContent = '\u00B7';
        corner.style.color = 'var(--text-muted)';
        headerRow.appendChild(corner);

        for (let j = 0; j < data.size; j++) {
            const th = document.createElement('th');
            th.textContent = data.names[j];
            th.className = 'ct-' + data.roles[j];
            th.title = data.names[j] + ' (' + data.roles[j] + ')';
            this.colHeaders.push(th);
            headerRow.appendChild(th);
        }
        thead.appendChild(headerRow);
        table.appendChild(thead);

        // Body
        const tbody = document.createElement('tbody');
        for (let i = 0; i < data.size; i++) {
            const row = document.createElement('tr');
            const th = document.createElement('th');
            th.textContent = data.names[i];
            th.className = 'ct-' + data.roles[i];
            th.title = data.names[i] + ' (' + data.roles[i] + ')';
            this.rowHeaders.push(th);
            row.appendChild(th);

            this.cells[i] = [];
            for (let j = 0; j < data.size; j++) {
                const td = document.createElement('td');
                const resultIdx = data.cells[i][j];
                td.textContent = data.names[resultIdx];
                td.title = data.names[i] + ' \u00B7 ' + data.names[j] + ' = ' + data.names[resultIdx];
                td.dataset.row = i;
                td.dataset.col = j;
                td.addEventListener('click', () => {
                    if (this.onCellClick) this.onCellClick(i, j, resultIdx);
                });
                this.cells[i][j] = td;
                row.appendChild(td);
            }
            tbody.appendChild(row);
        }
        table.appendChild(tbody);
        this.container.appendChild(table);
    }

    /**
     * Highlight a specific operation: row (left operand), col (right operand).
     * Returns { left, right, result } names.
     */
    highlight(row, col) {
        this.clearHighlight();
        if (!this.data || row < 0 || col < 0 || row >= this.data.size || col >= this.data.size) return null;

        this.hlRow = row;
        this.hlCol = col;

        // Highlight row
        this.rowHeaders[row].classList.add('ct-hl-header');
        for (let j = 0; j < this.data.size; j++) {
            this.cells[row][j].classList.add('ct-hl-row');
        }

        // Highlight column
        this.colHeaders[col].classList.add('ct-hl-header');
        for (let i = 0; i < this.data.size; i++) {
            this.cells[i][col].classList.add('ct-hl-col');
        }

        // Highlight result cell
        this.cells[row][col].classList.add('ct-hl-result');

        // Scroll into view
        this.cells[row][col].scrollIntoView({ block: 'nearest', inline: 'nearest' });

        const resultIdx = this.data.cells[row][col];
        return {
            left: this.data.names[row],
            right: this.data.names[col],
            result: this.data.names[resultIdx]
        };
    }

    clearHighlight() {
        if (this.hlRow >= 0 && this.data) {
            this.rowHeaders[this.hlRow].classList.remove('ct-hl-header');
            for (let j = 0; j < this.data.size; j++) {
                this.cells[this.hlRow][j].classList.remove('ct-hl-row');
            }
        }
        if (this.hlCol >= 0 && this.data) {
            this.colHeaders[this.hlCol].classList.remove('ct-hl-header');
            for (let i = 0; i < this.data.size; i++) {
                this.cells[i][this.hlCol].classList.remove('ct-hl-col');
            }
        }
        if (this.hlRow >= 0 && this.hlCol >= 0 && this.data) {
            this.cells[this.hlRow][this.hlCol].classList.remove('ct-hl-result');
        }
        this.hlRow = -1;
        this.hlCol = -1;
    }

    /**
     * Look up an atom name → index.
     */
    nameToIndex(name) {
        if (!this.data) return -1;
        return this.data.names.indexOf(name);
    }

    /**
     * Highlight by atom names: left · right = result.
     */
    highlightByName(leftName, rightName) {
        const row = this.nameToIndex(leftName);
        const col = this.nameToIndex(rightName);
        if (row >= 0 && col >= 0) return this.highlight(row, col);
        return null;
    }
}
