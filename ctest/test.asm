	ljmp main						;
	
	.org 100h
	main:
	setb p3.1
	ljmp main
