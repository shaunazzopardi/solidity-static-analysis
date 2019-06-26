contract CourierService{

    address owner;

    mapping(address => uint) fees;

    mapping(uint => address) customer;
    mapping(uint => uint) orderETA;
    mapping(uint => uint) orderDeliveryTime;
    mapping(uint => bool) delivered;
    mapping(uint => bool) ordered;

    mapping(uint => bool) cancelled;

    mapping(address => uint) extraTimeAllowance;
    uint cost;

    function CourierService() public{
      owner = msg.sender;
    }


    function order(uint orderNo, uint eta) payable public{
        require(msg.value >= cost);
        require(!ordered[orderNo]);

        customer[orderNo] = msg.sender;
        orderETA[orderNo] = eta;
        ordered[orderNo] = true;
    }

    function delivery(uint orderNo) public{
        require(msg.sender == customer[orderNo]);
        require(ordered[orderNo] && !delivered[orderNo]);

        delivered[orderNo] = true;

        orderDeliveryTime[orderNo] = now;
    }

    function refund(uint orderNo) public payable{
        require(ordered[orderNo] && !delivered[orderNo] && !cancelled[orderNo]);
        require(msg.sender == owner);

        transferTo(cost, orderNo);
        cancelled[orderNo] = true;
    }

    function transferTo(uint val, uint orderNo) public payable{
        require(msg.sender == owner);

        customer[orderNo].call.value(val);
    }
}
