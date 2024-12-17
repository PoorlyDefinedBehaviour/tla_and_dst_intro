package main

import (
	"database/sql"
	"encoding/json"
	"net/http"

	_ "github.com/go-sql-driver/mysql"
	"github.com/gorilla/mux"
)

type Bank struct{ db *sql.DB }

func NewBank(db *sql.DB) *Bank {
	return &Bank{db: db}
}

type transferInput struct {
	From   string `json:"from"`
	To     string `json:"to"`
	Amount int    `json:"amount"`
}

type depositInput struct {
	From   string `json:"from"`
	Amount int    `json:"amount"`
}

type withdrawInput struct {
	From   string `json:"from"`
	Amount int    `json:"amount"`
}

func (b *Bank) transferHandler(w http.ResponseWriter, r *http.Request) {
	var input transferInput
	if err := json.NewDecoder(r.Body).Decode(&input); err != nil {
		w.WriteHeader(500)
		return
	}

	tx, err := b.db.Begin()
	if err != nil {
		w.WriteHeader(500)
		return
	}
	defer tx.Rollback()

	row := tx.QueryRow("SELECT balance FROM balances WHERE id = ?", input.From)
	var balance int
	if err := row.Scan(&balance); err != nil {
		w.WriteHeader(500)
		return
	}

	if balance-input.Amount < 0 {
		return
	}

	if _, err := tx.Exec("UPDATE balances SET balance = balance - ? WHERE id = ?", input.Amount, input.From); err != nil {
		w.WriteHeader(500)
		return
	}
	if _, err := tx.Exec("UPDATE balances SET balance = balance + ? WHERE id = ?", input.Amount, input.To); err != nil {
		w.WriteHeader(500)
		return
	}

	if err := tx.Commit(); err != nil {
		w.WriteHeader(500)
		return
	}
}

func (b *Bank) depositHandler(w http.ResponseWriter, r *http.Request) {
	var input depositInput
	if err := json.NewDecoder(r.Body).Decode(&input); err != nil {
		w.WriteHeader(500)
		return
	}

	_, err := b.db.Exec("UPDATE balances SET balance = balance + ? WHERE id = ?", input.Amount, input.From)
	if err != nil {
		w.WriteHeader(500)
		return
	}
}

func (b *Bank) withdrawHandler(w http.ResponseWriter, r *http.Request) {
	var input depositInput
	if err := json.NewDecoder(r.Body).Decode(&input); err != nil {
		w.WriteHeader(500)
		return
	}

	tx, err := b.db.Begin()
	if err != nil {
		w.WriteHeader(500)
		return
	}
	defer tx.Rollback()

	row := tx.QueryRow("SELECT balance FROM balances WHERE id = ?", input.From)
	var balance int
	if err := row.Scan(&balance); err != nil {
		w.WriteHeader(500)
		return
	}

	if balance-input.Amount < 0 {
		return
	}

	_, err = tx.Exec("UPDATE balances SET balance = balance - ? WHERE id = ?", input.Amount, input.From)
	if err != nil {
		w.WriteHeader(500)
		return
	}

	if err := tx.Commit(); err != nil {
		w.WriteHeader(500)
		return
	}
}

func main() {
	db, err := sql.Open("mysql", "root:password@tcp(127.0.0.1:3306)/dev")
	if err != nil {
		panic(err.Error())
	}
	defer db.Close()

	bank := NewBank(db)

	r := mux.NewRouter()
	r.HandleFunc("/transfer", http.HandlerFunc(bank.transferHandler))
	r.HandleFunc("/deposit", http.HandlerFunc(bank.depositHandler))
	r.HandleFunc("/withdraw", http.HandlerFunc(bank.withdrawHandler))

	server := http.Server{Addr: "127.0.0.1:9001", Handler: r}
	if err := server.ListenAndServe(); err != nil {
		panic(err.Error())
	}
}
