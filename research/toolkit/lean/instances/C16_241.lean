import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 241 of the cap-16 certificate: slots 246784 .. 247807 -/
theorem chk_241 : chunkCheck 16 T stdSt 246784 1024 = true := by decide +kernel

end Row16
