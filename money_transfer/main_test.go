package main

import (
	"bytes"
	"database/sql"
	"encoding/json"
	"net/http/httptest"
	"sync"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"pgregory.net/rapid"
)

const (
	OpTransfer = "transfer"
	OpDeposit  = "deposit"
	OpWithdraw = "withdraw"
)

func TestBasic(t *testing.T) {
	t.Parallel()

	initialBalance := 1
	accounts := []string{"alice", "bob"}

	db, err := sql.Open("mysql", "root:password@tcp(127.0.0.1:3306)/dev")
	require.NoError(t, err)

	rapid.Check(t, func(t *rapid.T) {
		bank := NewBank(db)

		ops := rapid.SliceOfN(rapid.SampledFrom([]string{OpTransfer}), 1, 10).Draw(t, "ops")

		wg := &sync.WaitGroup{}
		wg.Add(len(ops))

		_, err = db.Exec("UPDATE balances SET balance = ?", initialBalance)
		require.NoError(t, err)

		for _, op := range ops {
			switch op {
			case OpTransfer:
				from := rapid.SampledFrom(accounts).Draw(t, "from")
				var to string
				if from == "alice" {
					to = "bob"
				} else {
					to = "alice"
				}

				duration := rapid.IntRange(0, 10).Draw(t, "sleep")
				go func(wg *sync.WaitGroup, from, to string) {
					defer wg.Done()
					time.Sleep(time.Duration(duration) * time.Millisecond)
					buffer, err := json.Marshal(transferInput{From: from, To: to, Amount: 1})
					require.NoError(t, err)
					r := httptest.NewRequest("POST", "http://127.0.0.1:9001/transfer", bytes.NewReader(buffer))
					w := httptest.NewRecorder()
					bank.transferHandler(w, r)
				}(wg, from, to)

			case OpDeposit:
				from := rapid.SampledFrom(accounts).Draw(t, "from")

				go func(wg *sync.WaitGroup, from string) {
					defer wg.Done()
					buffer, err := json.Marshal(depositInput{From: from, Amount: 1})
					require.NoError(t, err)
					r := httptest.NewRequest("POST", "http://127.0.0.1:9001/deposit", bytes.NewReader(buffer))
					w := httptest.NewRecorder()
					bank.depositHandler(w, r)
				}(wg, from)
			case OpWithdraw:
				from := rapid.SampledFrom(accounts).Draw(t, "from")

				go func(wg *sync.WaitGroup, from string) {
					defer wg.Done()
					buffer, err := json.Marshal(withdrawInput{From: from, Amount: 1})
					require.NoError(t, err)
					r := httptest.NewRequest("POST", "http://127.0.0.1:9001/withdraw", bytes.NewReader(buffer))
					w := httptest.NewRecorder()
					bank.withdrawHandler(w, r)
				}(wg, from)
			}
		}

		wg.Wait()

		// Assert db state is valid
		var totalBalance int
		require.NoError(t, db.QueryRow("SELECT SUM(balance) FROM balances").Scan(&totalBalance))
		assert.Equal(t, initialBalance*len(accounts), totalBalance)

		var accountsWithNegativeBalance int
		require.NoError(t, db.QueryRow("SELECT COUNT(id) FROM balances WHERE balance < 0").Scan(&accountsWithNegativeBalance))
		assert.Equal(t, 0, accountsWithNegativeBalance)
	})
}
