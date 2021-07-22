
// SPDX-License-Identifier: NULL

pragma solidity ^0.7.6;


contract ItokenTimeLock{
  
   event tokenLocked(address indexed  tokenAddress ,address indexed locker , address indexed owner ,  uint256 amount , uint256 unlockTime, uint256 lockID);
    event tokenUnLocked(address indexed tokenAddress, address indexed reciever , uint256 amount , uint256 lockID  );
    event tokenMigrated(address indexed tokenAddress, address indexed oldOwner , address indexed newOwner  , uint256 lockID  );
   
    //provide either pair address or token1 and token2 address;
    function locktoken(address _tokenAddress  ,  uint256 amount ,  uint256 periodInHR , address _reciever ) external payable;
    
    
    
    function unLocktoken(address _tokenAddress , uint256 lockID) external;
    function migratetoken(address _tokenAddress , uint256 lockID , address to) external;
    
    function getActivetokenLockIDs(address _tokenAddress) external view returns(uint256[] memory);
    function getTotalLocksValue(address _tokenAddress)external view returns(uint256);
    function getTotalLocksBalance(address _tokenAddress)external view returns(uint256);

    function getUsertokenLocksAddress() external view returns(address[] memory);
   
    
}
