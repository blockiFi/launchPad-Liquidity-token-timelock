

pragma solidity ^0.7.6;


 interface ILiquidityTimeLock {
     
    event liquidityLocked(address indexed pairAddress ,address indexed locker , address indexed owner ,  uint256 amount , uint256 unlockTime, uint256 lockID);
    event liquidityUnLocked(address indexed pairAddress, address indexed reciever , uint256 amount , uint256 lockID  );
    event liquidityMigrated(address indexed pairAddress, address indexed oldOwner , address indexed newOwner  , uint256 lockID  );
    
    function lockLiquidity(address _pairAddress ,address token1 , address token2  ,  uint256 amount ,  uint256 periodInHR , address _reciever ) external payable;
    
    function unLockLiquidity(address _pairAddress , uint256 lockID) external ;
    
    function migrateLiquidity(address _pairAddress , uint256 lockID , address to) external;
    
    function getActiveLPLockIDs(address _pairAddress) external view returns(uint256[] memory);
    
    function getTotalLocksValue(address _pairAddress)external view returns(uint256);
    function getTotalLocksBalance(address _pairAddress)external view returns(uint256);
    function getPairAddress(address token1 , address token2) external  view returns(address);
    function getTokens(address _pairAddress) external view returns(address token1 ,address token2);
    
   
}
