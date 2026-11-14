import EthBridge.Anthropic

#check @EthBridge.Anthropic.not_eth_of_ethIsFalse
#check @ComplexityAbstracts.SubexponentialSATAbstract.not_eth
#check MainResults.ETHIsFalse

example (h : MainResults.ETHIsFalse) :
    ¬ ComplexityAbstracts.SubexponentialSATAbstract.ETH :=
  EthBridge.Anthropic.not_eth_of_ethIsFalse h

#print axioms EthBridge.Anthropic.not_eth_of_ethIsFalse
#print axioms ComplexityAbstracts.SubexponentialSATAbstract.not_eth
