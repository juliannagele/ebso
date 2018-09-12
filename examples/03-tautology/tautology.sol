pragma solidity ^0.4.0;

contract Tautology {

  function f (bool b) public returns (bool) {
    if (b || !b) {
      return true;
    }
    else {
      return false;
    }
  }
  
}
