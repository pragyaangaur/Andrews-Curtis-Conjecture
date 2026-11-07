import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 191 of the cap-16 certificate: slots 195584 .. 196607 -/
theorem chk_191 : chunkCheck 16 T stdSt 195584 1024 = true := by decide +kernel

end Row16
