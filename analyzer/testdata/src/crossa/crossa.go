package crossa // want package:"structs \\[Account Amount Kinds\\] contracts \\[Deactivate New Parse SameKinds Sum USD Wrong\\]"

import "errors"

// Библиотека для межпакетных тестов: спецификации и сводки экспортируются
// фактом пакета.

const RUB = "rub"

const usd = "usd"

// @ bound <c string>;
type Amount struct {
	// @ equals c;
	Currency string
	Value    float64
}

// @ requires a<c> == b<c>;
// @ returns Amount<a<c>>;
func Sum(a, b Amount) Amount { return Amount{Currency: a.Currency, Value: a.Value + b.Value} }

// @ returns Amount<c>;
func New(c string, v float64) Amount { return Amount{Currency: c, Value: v} }

// Неэкспортированная константа в контракте: передаётся значением.
// @ returns Amount<usd>;
func USD(v float64) Amount { return Amount{Currency: usd, Value: v} }

// @ ensures err == nil ==> res<c> == c;
func Parse(c, raw string) (res Amount, err error) {
	if raw == "" {
		return Amount{}, errors.New("empty")
	}
	return Amount{Currency: c}, nil
}

type Status string

const (
	StatusActive   Status = "active"
	StatusInactive Status = "inactive"
)

// @ bound <s Status>;
type Account struct {
	// @ equals s;
	Status Status
	Name   string
}

// @ requires a<s> == StatusActive;
// @ ensures a<s> == StatusInactive;
func Deactivate(a *Account) { a.Status = StatusInactive }

func NewAccount() *Account { return &Account{Status: StatusActive} }

func Touch(a *Account) Status { return a.Status }

func Rename(a *Account, name string) { a.Name = name }

var registry []*Account

func Keep(a *Account) { registry = append(registry, a) }

type Order struct {
	Acc *Account
}

func Attach(o *Order, a *Account) { o.Acc = a }

func (o *Order) Account() *Account { return o.Acc }
