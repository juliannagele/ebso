pragma solidity ^0.4.0;

contract Zero {

function f (uint8 x) public pure returns (uint8) {
  return 42 + (0 - x);
}

}
