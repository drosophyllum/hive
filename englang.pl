use Data::Dumper;
$_= shift;
open(DATA,$_);
$_=join "", <DATA>;

@_ = split /\./ ,$_;
for (@_){
	$that = "";
	while(/([a-zA-Z]+)/g){
	##	print $1,$/;
		$this= lc $1;
		if ($that){
			push @out, [$that,$this];}
		$that = $this;
		
	}
}

for (@out) {
	($this,$that) = @$_;
	print "$this.$this => $that.$that;\n";
}
