pragma solidity ^0.4.0;

contract Inline {

  function c public pure returns (uint8) {
    return 42;
  }

  function f (uint8 x) public returns (uint8) {
    return x + c;
  }
}
