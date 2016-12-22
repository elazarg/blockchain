
contract DealBuilder {
    ResourceManager[] managers;
    function add(ResourceManager m) {
        managers.push(m);
    }

    function deal() {
        for (uint i=0; i < managers.length; i++) {
            managers[i].publish(managers);
        }
    }
}

contract ResourceManager {
    function perform_one(uint index) internal;

    uint last;
    Interested[20] involved;
    function publish(ResourceManager[] managers) {
        for (uint j=0; j < last; j++)
            involved[j].verify_deal(managers);
    }

    function push(Interested a) internal {
        involved[last++] = a;
    }
    
    function perform() {
        while (last > 0) {
            perform_one(last);
            delete involved[last];
            last--;
        }
    }
}

contract Coin is ResourceManager {
    mapping(address => uint256) public balances;
    
    uint256[] new_balances;
    
    function propose(Interested a, uint256 value) {
        push(a);
        new_balances.push(value);
    }
    
    function perform_one(uint index) internal {
        balances[involved[index]] = new_balances[index];
        delete new_balances[index];
    }
}

contract Token is ResourceManager {
    address token_owner;
    
    function propose(Interested owner) {
        push(owner);
    }
    
    function perform_one(uint index) internal {
        token_owner = involved[index];
        delete involved[index];
    }
}

contract Allocator is ResourceManager {
    mapping(string => address) names;
    
    string[] new_names;
    
    function propose(string name, Interested named) {
        new_names.push(name);
        push(named);
    }
    
    function perform_one(uint index) internal {
        names[new_names[index]] = involved[index];
        delete new_names[index];
    }
}

contract StandaloneDeal { }

contract ExchangeToken is StandaloneDeal {
    struct Row {
        Coin selling; uint sell_amount;
        Coin buying;  uint buy_amount;
    }
    
    mapping(bytes32 => Interested) deals;
    mapping(address => Row) seller;
    
    function add_deal(Coin selling, uint sell_amount, Coin buying, uint buy_amount) {
        Row memory r = Row(selling, sell_amount, buying, buy_amount);
        Row memory rev = Row(buying, buy_amount, selling, sell_amount);
        var sender = Interested(msg.sender);
        var buyer = deals[sha3(rev)];
        if (buyer != address(0x0)) {
            selling.propose(sender, selling.balances(sender) - sell_amount);
            selling.propose(buyer, selling.balances(buyer) + sell_amount);
            buying.propose(sender, selling.balances(sender) + buy_amount);
            buying.propose(buyer, selling.balances(buyer) - buy_amount);
            ResourceManager[] storage managers;
            managers.push(selling);
            managers.push(buying);
            Hub.deal(managers);
        } else {
            deals[sha3(r)] = sender;
            seller[sender] = r;
        }
    }
}

contract PersistentBillboard {
    mapping(address => uint[]) deals;
    
    function propose(uint deal) {
        deals[msg.sender].push(deal);
    }
}

contract Interested {
    function verify_deal(ResourceManager[]);
}

contract Client is Interested {
    
}
