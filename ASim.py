import queue
import random
import hashlib
from ecdsa import SigningKey
import threading
import time
# from scipy.special import comb
from threading import Semaphore
import time
import math

class Block:

	def __init__(self, prevhash, rnd_bytes, typec, data=bytes(0)):
		# prevhash, rnd_bytes and header are of type bytes
		# bytes(32) in rnd_bytes signifies empty block
		self.header =  prevhash + rnd_bytes
		self.data = data
		self.typec = typec # final or tentative

class Barrier:
	def __init__(self):
		global N
		self.numthread = N
		self.structlock = Semaphore(1)
		self.thrlock = [Semaphore(0) for i in range(0, self.numthread)]
		self.barred = 0 # number of threads reached the fence

	def sem_wait(self, nid):
		global glbround
		# print str(NodeId)+" called sem_wait"
		# sys.stdout.flush()
		self.structlock.acquire()
		self.barred += 1
		if(self.barred==self.numthread):
			glbround += 1
			self.barred = 0 
			print ("starting ROUND "+str(glbround))
			# sys.stdout.flush()
			for i in range(0,self.numthread):
				self.thrlock[i].release()
		self.structlock.release()
		self.thrlock[nid].acquire()


genblock = Block(bytes(32), bytes(32), 1,"We are building the best Algorand Discrete Event Simulator".encode("utf-8"))
N = 10 # number of node
gblprng, glbround = random.Random(), 1
node = []
mu_blk, sigma_blk, mu_nonblk, sigma_nonblk = 200, 400, 30, 64
tau_proposer, tau_step, tau_final = 20, 20, 20 # TODO
lambda_proposer, lambda_blk, lambda_step =  10, 10, 10
threshold_step, threshold_final = 0.67, 0.67 # TODO
sum_stakes = 0
MAXSTEPS = 15
brexit = False
barrier = Barrier()
temp_threads = queue.Queue(0)
byz_mesg = [None, None, 0]
byz_sem = Semaphore(1)

def calc_SHA256(s):
	# s = bytes
	sha_256 = hashlib.sha256()
	sha_256.update(s)
	byts = sha_256.digest()
	return byts

def PRG(seed):
	# seed is of type bytes, return bytes
	local_prng = random.Random(seed)
	num = local_prng.getrandbits(256)
	return num.to_bytes(32, 'little')
	# return num

class Link:

	def __init__(self, a, bd, nbd):
		self.endpoint = a
		self.blk_delay = bd
		self.nonblk_delay = nbd


choose = [[-1 for i in range(55)] for j in range(55)]

def fillchoose():
	choose[1][0] = choose[1][1] = choose[0][0] = 1
	for i in range(2, 52+1):
		choose[i][0] = choose[i][i] = 1
		for j in range(1, i):
			choose[i][j] = choose[i-1][j-1] + choose[i-1][j]


# IMP: no member variable of Message should be changed after initialization
class Message:

	def __init__(self, payload, originator, mesg_id, signature, blk_nonblk):
		self.type = blk_nonblk
		self.OP = originator
		self.mesg_seq = mesg_id # int
		self.sign = signature
		self.payload = payload
		# self.sender = _from # specified by the recv channel itself

class Payload:

	def __init__(self, ptype, byts):
		self.type = ptype
		self.byts = byts

class PriorityPayload(Payload):

	def __init__(self, round_num, vrf_output, sub_userid, priority):
		self.round = round_num
		self.vrf_output = vrf_output
		self.sub_userid = sub_userid
		self.priority = priority
		byts = self.round.to_bytes(4, 'little') + vrf_output + self.sub_userid.to_bytes(4, 'little') + priority
		Payload.__init__(self, 0, byts)

class BlkPayload(Payload):

	def __init__(self, prevhash, rnd_num, priority_payload):
		self.prevhash = prevhash
		self.random = rnd_num
		self.prio_pl = priority_payload
		self.blkhash = calc_SHA256(prevhash+rnd_num)
		byts = prevhash + self.random + self.prio_pl.byts+self.blkhash
		Payload.__init__(self, 1, byts)

class VotePayload(Payload):

	def __init__(self, prevhash, round, step, num_votes, vrf_output, blkhash):
		self.prevhash = prevhash
		self.round_num = round
		self.step = step
		self.num_votes = num_votes
		self.blkhash = blkhash
		self.vrf_output = vrf_output
		byts = self.prevhash+round.to_bytes(4, 'little')+step.to_bytes(4, 'little')+num_votes.to_bytes(4, 'little')+blkhash+vrf_output
		Payload.__init__(self, 2, byts)

class RoundInfo:

	def __init__(self, prevhash, round_num):
		global MAXSTEPS
		self.prevhash = prevhash
		self.round_num = round_num
		self.step = 0 # current step
		self.maxprio = ((1<<256)-1).to_bytes(32, 'little')
		self.mpuid = -1
		
		self.rtime_st = time.time()
		self.inc_mesg = [queue.Queue(0) for i in range(0, 4+MAXSTEPS)] # sem not needed to access
		self.blkprio = ((1<<256)-1).to_bytes(32, 'little')
		self.blkhash = bytes(32) # max priority payload till now
		# for documentation purposes
		self.prio_recv = {}
		self.blk_recv = {}

class Node:
	"""docstring for Node"""
	def __init__(self, _nid):
		global sum_stakes
		self.nid = _nid
		self.prng = random.Random(self.nid)
		self.recvq = queue.Queue(0)
		self.sendq = queue.Queue(0)
		self.stake = self.prng.randint(1, 50)
		sum_stakes += self.stake
		self.blockchain = [genblock]
		self.m = self.prng.randint(4,8)
		self.conn = []
		self.sk = SigningKey.generate()
		self.pk = self.sk.get_verifying_key()
		self.mesg_seq = 0
		self.seen_mesg = set()
		# TODO INVARIANT MAINTAIN of round info
		self.rinfo = RoundInfo(calc_SHA256(genblock.header+genblock.data), 1)
		self.rsem = Semaphore(1)
		self.f = open("./log/log_"+str(self.nid)+".txt", 'w')

	# returns vrf_output (bytes), #sub_user
	def sortition(self, tau):
		global sum_stakes, choose
		# self.rsem.acquire()
		seed = self.rinfo.prevhash + self.rinfo.round_num.to_bytes(4, 'little') + self.rinfo.step.to_bytes(4, 'little')
		# self.rsem.release()
		vrf_output = self.sign(PRG(seed))
		p, j, w = tau/sum_stakes, 0, self.stake
		ivrf = int.from_bytes(vrf_output, 'big')
		roulette = (ivrf*1.0)/(1<<384)
		ll, ul = 0, choose[w][j]*math.pow(1-p, w-j)*1 # TODO if required approx. maht.pow, falsein comb
		while not(roulette>=ll and roulette<ul):
			j+=1
			ll = ul
			ul += choose[w][j]*math.pow(1-p, w-j)*math.pow(p, j)
			if(j==w):
				break
		print ("sortition result for round {} & step {}: j = {}, vrf_output = {}".format(self.rinfo.round_num, self.rinfo.step, j, vrf_output[0:8]), file=self.f, flush=True)
		return (vrf_output, j)

	def sign(self, byts):
		# returns object of type bytes, always 48 bytes
		return self.sk.sign(byts)

	def highest_priority(self, vrf_output, j):
		hp = ((1<<256)-1).to_bytes(32, 'little')
		idx = -1
		for i in range(0,j):
			p = calc_SHA256(vrf_output + i.to_bytes(4, 'little'))
			if p < hp:
				hp = p
				idx = i
		# self.rsem.acquire()
		# if(hp < self.rinfo.maxprio):
		# 	self.rinfo.maxprio = hp
		# 	self.rinfo.mpuid = (self.nid, idx)
		# self.rsem.release()
		return (hp, idx)

	def recv(self):
		# run on a seperate thread
		global node,  brexit
		while not brexit:
			mesg, sender = self.recvq.get()  # blk until 
			if ( (mesg.mesg_seq, mesg.OP) in self.seen_mesg):
				continue
			if not node[mesg.OP].pk.verify(mesg.sign, mesg.payload.byts):
				print ("MESSAGE REJECTED. INCORRECT SIGNATURE")
				continue
			propogate = self.process(mesg, sender)
			# spreading gossip
			if (propogate):
				for l in self.conn:
					if l.endpoint != sender:
						self.sendq.put( (mesg, l) )

	def send(self):
		# run on seperate thread
		global temp_threads
		while not brexit:
			mesg, l = self.sendq.get()
			t = threading.Thread(target=self.send_mesg, args = (mesg, l, ))
			t.start()
			temp_threads.put(t)

	def send_mesg(self, mesg, l):
		# run on seperate thread
		global node
		tw = l.blk_delay if mesg.type==1 else l.nonblk_delay
		time.sleep(tw/1000)
		node[l.endpoint].recvq.put( (mesg, self.nid) )

	def gossip(self, mesg):
		# gossip the self generated message
		for l in self.conn:
			self.sendq.put( (mesg, l) )
		self.recvq.put( (mesg, self.nid) )

	def process(self, mesg, sender):
		# returns a bool which tells whether to propogate further
		self.seen_mesg.add((mesg.mesg_seq, mesg.OP))
		notme = mesg.OP!=self.nid
		self.rsem.acquire()
		if(mesg.payload.type == 0):
			# priority message
			if(time.time() > self.rinfo.rtime_st + lambda_proposer):
				self.rsem.release()
				return 1 & notme
			if(mesg.payload.round == self.rinfo.round_num):  # EXTRA next round mesg?
				self.rinfo.prio_recv[mesg.payload.priority] = (mesg.payload, mesg.OP)
				if (mesg.payload.priority < self.rinfo.maxprio):
					self.rinfo.maxprio = mesg.payload.priority
					self.rinfo.mpuid = (mesg.OP, mesg.payload.sub_userid)
					self.rsem.release()
					return 1 & notme
			self.rsem.release()
			return 0 # discards message with now priority than max prio seen 
		if(mesg.payload.type == 1):
			# Block proposal message
			if(time.time() > self.rinfo.rtime_st + lambda_proposer+lambda_blk):
				self.rsem.release()
				return 1 & notme
			if(mesg.payload.prio_pl.round == self.rinfo.round_num):
				self.rinfo.blk_recv[mesg.payload.blkhash] = (mesg.payload, mesg.OP)
				if (mesg.payload.prio_pl.priority < self.rinfo.blkprio):
					self.rinfo.blkprio = mesg.payload.prio_pl.priority
					self.rinfo.blkhash = mesg.payload.blkhash
					self.rsem.release()
					return 1 & notme
			self.rsem.release()
			return 0
		if(mesg.payload.type == 2):
			# vote message
			if(mesg.payload.round_num == self.rinfo.round_num):
				self.rinfo.inc_mesg[mesg.payload.step].put(mesg)
				print("received {} votes for {} in round {} & step {} by {}".format(mesg.payload.num_votes, mesg.payload.blkhash[0:8], mesg.payload.round_num, mesg.payload.step, mesg.OP), file=self.f)
			self.rsem.release()
			return 1 & notme
		self.rsem.release()
		assert(False)

	def committeeVote(self, tau, blkhash):
		vrf_output, j = self.sortition(tau)
		if(j>0):
			mesg = self.gen_vote_mesg(j, vrf_output, blkhash)
			self.gossip(mesg)
			# TODO send yourself the vote

	def countVotes(self, step, thr, tau, wait_time, toss=False):
		# rsem not used see if its correct
		st = time.time()
		cnts = {}
		voters = set()
		minhash = ((1<<256) - 1).to_bytes(32, 'little')
		while True:
			try:
				mesg = self.rinfo.inc_mesg[step].get(block=True, timeout=.05) # AWARE timeout hardcode
			except queue.Empty:
				if(time.time() > st+wait_time):
					print("result for step {} round {} is {} ".format(step, self.rinfo.round_num, "TIMEOUT"), file=self.f)
					for key, val in cnts.items():
						print("got {} votes for {}, req {}, in step {} round {}".format(val, key[0:6],  math.ceil(thr*tau), step, self.rinfo.round_num), file=self.f, flush=True)
					if toss:
						return (-1, minhash[31] % 2) 
					return -1
				continue
			if (mesg.payload.prevhash != self.rinfo.prevhash) or (mesg.OP in voters):
				continue
			voters.add(mesg.OP)
			v = cnts.get(mesg.payload.blkhash,0)
			cnts[mesg.payload.blkhash] = v + mesg.payload.num_votes
			if toss:
				for j in range(1, mesg.payload.num_votes+1):
					p = calc_SHA256(mesg.payload.vrf_output + j.to_bytes(4, 'little'))
					if p < minhash:
						minhash = p
			if( cnts[mesg.payload.blkhash] >= thr*tau):
				print("result for step {} round {} is {} ".format(step, self.rinfo.round_num, mesg.payload.blkhash[0:6]), file=self.f, flush=True)
				if toss:
					return (mesg.payload.blkhash, minhash[31] % 2)
				return mesg.payload.blkhash

	def reduction(self, blkhash):
		global tau_step, threshold_step
		self.committeeVote(tau_step, blkhash)
		h1hash = self.countVotes(self.rinfo.step, threshold_step, tau_step, lambda_step+lambda_blk) # TODO confirm the wait time in paper/assign
		if h1hash == -1:
			h1hash = bytes(32)
		self.rinfo.step += 1
		self.committeeVote(tau_step, h1hash)
		h2hash = self.countVotes(self.rinfo.step, threshold_step, tau_step, lambda_step) # TODO above
		self.rinfo.step += 1
		if h2hash==-1:
			return bytes(32)
		return h2hash

	def binaryBA(self, blkhash):
		global MAXSTEPS
		assert(self.rinfo.step == 3), "error assertion round Number is "+str(self.rinfo.step)
		r = blkhash
		empty_hash = bytes(32)
		while(self.rinfo.step < MAXSTEPS+3):
			self.committeeVote(tau_step, r)
			r = self.countVotes(self.rinfo.step, threshold_step, tau_step, lambda_step)
			if r== -1:
				r = blkhash
			elif r != empty_hash:
				if self.rinfo.step == 3:
					self.rinfo.step = MAXSTEPS+3
					self.committeeVote(tau_final, r) # do not run committee vote or its parts in a seperate thread
					self.rinfo.step = 3 # TODO see if consistency is maintained in messages
				for i in range(0,3):
					self.rinfo.step += 1
					self.committeeVote(tau_step, r)
				return r
			self.rinfo.step+=1
			
			self.committeeVote(tau_step, r)
			r = self.countVotes(self.rinfo.step, threshold_step, tau_step, lambda_step)
			if r == -1:
				r = empty_hash
			elif r == empty_hash:
				for i in range(0,3):
					self.rinfo.step += 1
					self.committeeVote(tau_step, r)
				return r
			self.rinfo.step += 1

			self.committeeVote(tau_step, r)
			r, cc = self.countVotes(self.rinfo.step, threshold_step, tau_step, lambda_step, True)
			if r== -1:
				if cc == 0:
					r = empty_hash
				else: 
					r = blkhash
			self.rinfo.step += 1
		return 0
		# assert (False), "No Consensus reached in node "+str(self.nid)# no Consensus

	def node_main(self):
		global barrier
		print("node {} is up".format(self.nid))
		print("node {} init with {} stakes and connected to {}".format(self.nid, self.stake, [l.endpoint for l in self.conn]), file=self.f)
		tr = threading.Thread(target=self.recv)
		tr.start()
		ts = threading.Thread(target=self.send)
		ts.start()
		while True:
			vrf_output, j = self.sortition(tau_proposer)
			hp, idx = self.highest_priority(vrf_output, j)
			if (j>0):
				mesg = self.gen_prio_mesg(vrf_output, j, hp)
				self.gossip(mesg)
				# print ("{} is proposer for round {}".format(self.nid, self.rinfo.round_num))
			time.sleep(lambda_proposer)
			# update to maxprio will stop as lambda proposer has passed in sleep. 
			if (j>0 and hp <= self.rinfo.maxprio):
				# print ("highest priority in round {} is {} by {} accd to {}".format(self.rinfo.round_num, self.rinfo.maxprio, self.rinfo.mpuid, self.nid))
				mesg = self.gen_blk_mesg(vrf_output, j, hp)
				self.gossip(mesg)
			time.sleep(lambda_blk)
			self.rinfo.step+=1
			hblock = self.reduction(self.rinfo.blkhash)
			hblock_ = self.binaryBA(hblock)
			r = self.countVotes(3+MAXSTEPS, threshold_final, tau_final, lambda_step)
			blk = None
			if (hblock_ == r):
				blk = Block(self.rinfo.prevhash, calc_SHA256(r), 1) # rnd number = sha of block hash
			elif hblock_ == bytes(32):
				blk = Block(self.rinfo.prevhash, bytes(32), 0)
			else:
				blk = Block(self.rinfo.prevhash, calc_SHA256(hblock_), 0)
			print("\npriority messages received during round {}".format(self.rinfo.round_num), file=self.f)
			for key, val in self.rinfo.prio_recv.items():
				print("priority = {}, vrf_output = {}, sub_user_idx = {} by {}".format(key, val[0].vrf_output[0:8], val[0].sub_userid, val[1]), file=self.f)
			print("\nBlock proposal messages received during round {}".format(self.rinfo.round_num), file=self.f)
			for key, val in self.rinfo.blk_recv.items():
				print("block hash = {}, priority = {}, prevhash = {} by {}".format(key[0:8], val[0].prio_pl.priority, val[0].prevhash[0:8], val[1]), file=self.f)
			print ("\n{} Consensus acheived on block hash {} in round {}".format("FINAL" if blk.typec==1 else ("TENTATIVE" if hblock_!=0 else "NO"), hblock_, self.rinfo.round_num), file=self.f, flush=True)
			self.rsem.acquire()
			self.blockchain.append(blk)
			if hblock_ == bytes(32):
				self.rinfo = RoundInfo(calc_SHA256(blk.header+blk.data), self.rinfo.round_num+1)
			else:
				self.rinfo = RoundInfo(hblock_, self.rinfo.round_num+1)
			self.rsem.release()
			barrier.sem_wait(self.nid)

	def gen_prio_mesg(self, vrf_output, j, priority):
		# self.rsem.acquire()
		payload = PriorityPayload(self.rinfo.round_num, vrf_output, j, priority)
		mesg = Message(payload, self.nid, self.mesg_seq, self.sign(payload.byts), 0)
		self.mesg_seq+=1
		# self.rsem.release()
		return mesg

	def gen_blk_mesg(self, vrf_output, j, priority):
		# self.rsem.acquire()
		prio_pl = PriorityPayload(self.rinfo.round_num, vrf_output, j, priority) 
		payload = BlkPayload(self.rinfo.prevhash, (self.prng.getrandbits(256)).to_bytes(32,'little'), prio_pl)
		mesg = Message(payload, self.nid, self.mesg_seq, self.sign(payload.byts), 1)
		self.mesg_seq+=1
		# self.rsem.release()
		return mesg

	def gen_vote_mesg(self, num_votes, vrf_output, blkhash):
		# self.rsem.acquire()
		payload = VotePayload(self.rinfo.prevhash, self.rinfo.round_num, self.rinfo.step, num_votes, vrf_output, blkhash)
		mesg = Message(payload, self.nid, self.mesg_seq, self.sign(payload.byts), 0)
		self.mesg_seq+=1
		# self.rsem.release()
		return mesg

class FailStop(Node):

	def __init__(self, nid):
		Node.__init__(self, nid)

	def reduction(self, blkhash, stop=False):
		global tau_step, threshold_step
		if not stop:
			self.committeeVote(tau_step, blkhash)
		h1hash = self.countVotes(self.rinfo.step, threshold_step, tau_step, lambda_step+lambda_blk) # TODO confirm the wait time in paper/assign
		if h1hash == -1:
			h1hash = bytes(32)
		self.rinfo.step += 1
		if not stop:
			self.committeeVote(tau_step, h1hash)
		h2hash = self.countVotes(self.rinfo.step, threshold_step, tau_step, lambda_step) # TODO above
		self.rinfo.step += 1
		if h2hash==-1:
			return bytes(32)
		return h2hash

	def binaryBA(self, blkhash, stop=False):
		global MAXSTEPS
		assert(self.rinfo.step == 3), "error assertion round Number is "+str(self.rinfo.step)
		r = blkhash
		empty_hash = bytes(32)
		while(self.rinfo.step < MAXSTEPS+3):
			if not stop:
				self.committeeVote(tau_step, r)
			r = self.countVotes(self.rinfo.step, threshold_step, tau_step, lambda_step)
			if r== -1:
				r = blkhash
			elif r != empty_hash:
				if self.rinfo.step == 3:
					self.rinfo.step = MAXSTEPS+3
					if not stop:
						self.committeeVote(tau_final, r) # do not run committee vote or its parts in a seperate thread
					self.rinfo.step = 3 # TODO see if consistency is maintained in messages
				for i in range(0,3):
					self.rinfo.step += 1
					if not stop:
						self.committeeVote(tau_step, r)
				return r
			self.rinfo.step+=1
			if not stop:
				self.committeeVote(tau_step, r)
			r = self.countVotes(self.rinfo.step, threshold_step, tau_step, lambda_step)
			if r == -1:
				r = empty_hash
			elif r == empty_hash:
				for i in range(0,3):
					self.rinfo.step += 1
					if not stop:
						self.committeeVote(tau_step, r)
				return r
			self.rinfo.step += 1
			if not stop:
				self.committeeVote(tau_step, r)
			r, cc = self.countVotes(self.rinfo.step, threshold_step, tau_step, lambda_step, True)
			if r== -1:
				if cc == 0:
					r = empty_hash
				else: 
					r = blkhash
			self.rinfo.step += 1
		return 0
		# assert (False), "No Consensus reached in node "+str(self.nid)# no Consensus

	def node_main(self):
		global barrier
		print("node {} is up".format(self.nid))
		print("node {} init with {} stakes and connected to {}".format(self.nid, self.stake, [l.endpoint for l in self.conn]), file=self.f)
		tr = threading.Thread(target=self.recv)
		tr.start()
		ts = threading.Thread(target=self.send)
		ts.start()
		while True:
			vrf_output, j = self.sortition(tau_proposer)
			hp, idx = self.highest_priority(vrf_output, j)
			if (j>0):
				mesg = self.gen_prio_mesg(vrf_output, j, hp)
				self.gossip(mesg)
				# print ("{} is proposer for round {}".format(self.nid, self.rinfo.round_num))
			time.sleep(lambda_proposer)
			# update to maxprio will stop as lambda proposer has passed in sleep. 
			time.sleep(lambda_blk)
			self.rinfo.step+=1
			hblock = self.reduction(self.rinfo.blkhash, j>0)
			hblock_ = self.binaryBA(hblock, j>0)
			r = self.countVotes(3+MAXSTEPS, threshold_final, tau_final, lambda_step)
			blk = None
			if (hblock_ == r):
				blk = Block(self.rinfo.prevhash, calc_SHA256(r), 1) # rnd number = sha of block hash
			elif hblock_ == bytes(32):
				blk = Block(self.rinfo.prevhash, bytes(32), 0)
			else:
				blk = Block(self.rinfo.prevhash, calc_SHA256(hblock_), 0)
			print("\npriority messages received during round {}".format(self.rinfo.round_num), file=self.f)
			for key, val in self.rinfo.prio_recv.items():
				print("priority = {}, vrf_output = {}, sub_user_idx = {} by {}".format(key, val[0].vrf_output[0:8], val[0].sub_userid, val[1]), file=self.f)
			print("\nBlock proposal messages received during round {}".format(self.rinfo.round_num), file=self.f)
			for key, val in self.rinfo.blk_recv.items():
				print("block hash = {}, priority = {}, prevhash = {} by {}".format(key[0:8], val[0].prio_pl.priority, val[0].prevhash[0:8], val[1]), file=self.f)
			print ("\n{} Consensus acheived on block hash {} in round {}".format("FINAL" if blk.typec==1 else ("TENTATIVE" if hblock_!=0 else "NO"), hblock_, self.rinfo.round_num), file=self.f, flush=True)
			self.rsem.acquire()
			self.blockchain.append(blk)
			if hblock_ == bytes(32):
				self.rinfo = RoundInfo(calc_SHA256(blk.header+blk.data), self.rinfo.round_num+1)
			else:
				self.rinfo = RoundInfo(hblock_, self.rinfo.round_num+1)
			self.rsem.release()
			barrier.sem_wait(self.nid)

class Byznatine(Node):

	def __init__(self, nid):
		self.mode = 0
		self.vhash = None
		Node.__init__(self, nid)

	def process(self, mesg, sender):
		# returns a bool which tells whether to propogate further
		self.seen_mesg.add((mesg.mesg_seq, mesg.OP))
		notme = mesg.OP!=self.nid
		self.rsem.acquire()
		if(mesg.payload.type == 0):
			# priority message
			if(time.time() > self.rinfo.rtime_st + lambda_proposer):
				self.rsem.release()
				return 1 & notme
			if(mesg.payload.round == self.rinfo.round_num):  # EXTRA next round mesg?
				self.rinfo.prio_recv[mesg.payload.priority] = (mesg.payload, mesg.OP)
				if (mesg.payload.priority < self.rinfo.maxprio):
					self.rinfo.maxprio = mesg.payload.priority
					self.rinfo.mpuid = (mesg.OP, mesg.payload.sub_userid)
					self.rsem.release()
					return 1 & notme
			self.rsem.release()
			return 0 # discards message with now priority than max prio seen 
		if(mesg.payload.type == 1):
			# Block proposal message
			if(time.time() > self.rinfo.rtime_st + lambda_proposer+lambda_blk):
				self.rsem.release()
				return 1 & notme
			if(mesg.payload.prio_pl.round == self.rinfo.round_num):
				self.rinfo.blk_recv[mesg.payload.blkhash] = (mesg.payload, mesg.OP)
				if (mesg.payload.prio_pl.priority < self.rinfo.blkprio):
					self.rinfo.blkprio = mesg.payload.prio_pl.priority
					self.rinfo.blkhash = mesg.payload.blkhash
					self.rsem.release()
					adv = self.mode==0 or self.vhash==mesg.payload.blkhash
					return 1 & notme & adv
			self.rsem.release()
			return 0
		if(mesg.payload.type == 2):
			# vote message
			if(mesg.payload.round_num == self.rinfo.round_num):
				self.rinfo.inc_mesg[mesg.payload.step].put(mesg)
				print("received {} votes for {} in round {} & step {} by {}".format(mesg.payload.num_votes, mesg.payload.blkhash[0:8], mesg.payload.round_num, mesg.payload.step, mesg.OP), file=self.f)
			self.rsem.release()
			adv = self.mode==0 or self.vhash==mesg.payload.blkhash
			return 1 & notme & adv
		self.rsem.release()
		assert(False)

	def reduction(self, blkhash):
		global tau_step, threshold_step
		self.committeeVote(tau_step, blkhash)
		h1hash = self.countVotes(self.rinfo.step, threshold_step, tau_step, lambda_step+lambda_blk) # TODO confirm the wait time in paper/assign
		if h1hash == -1:
			h1hash = bytes(32)
		self.rinfo.step += 1
		self.committeeVote(tau_step, blkhash)
		h2hash = self.countVotes(self.rinfo.step, threshold_step, tau_step, lambda_step) # TODO above
		self.rinfo.step += 1
		if h2hash==-1:
			return bytes(32)
		return h2hash

	def binaryBA(self, blkhash):
		global MAXSTEPS
		assert(self.rinfo.step == 3), "error assertion round Number is "+str(self.rinfo.step)
		r = blkhash
		empty_hash = bytes(32)
		while(self.rinfo.step < MAXSTEPS+3):
			self.committeeVote(tau_step, blkhash)
			r = self.countVotes(self.rinfo.step, threshold_step, tau_step, lambda_step)
			if r== -1:
				r = blkhash
			elif r != empty_hash:
				if self.rinfo.step == 3:
					self.rinfo.step = MAXSTEPS+3
					self.committeeVote(tau_final, blkhash) # do not run committee vote or its parts in a seperate thread
					self.rinfo.step = 3 # TODO see if consistency is maintained in messages
				for i in range(0,3):
					self.rinfo.step += 1
					self.committeeVote(tau_step, blkhash)
				return r
			self.rinfo.step+=1
			
			self.committeeVote(tau_step, blkhash)
			r = self.countVotes(self.rinfo.step, threshold_step, tau_step, lambda_step)
			if r == -1:
				r = empty_hash
			elif r == empty_hash:
				for i in range(0,3):
					self.rinfo.step += 1
					self.committeeVote(tau_step, blkhash)
				return r
			self.rinfo.step += 1

			self.committeeVote(tau_step, blkhash)
			r, cc = self.countVotes(self.rinfo.step, threshold_step, tau_step, lambda_step, True)
			if r== -1:
				if cc == 0:
					r = empty_hash
				else: 
					r = blkhash
			self.rinfo.step += 1
		return 0
		# assert (False), "No Consensus reached in node "+str(self.nid)# no Consensus

	def lookout(self):
		st = time.time()
		while time.time()<st+lambda_blk:
			if byz_mesg[2]==self.rinfo.round_num:
				b = self.prng.randint(0,1)
				self.vhash = byz_mesg[b].payload.blkhash
				self.mode = 1
				return
			time.sleep(0.05)


	def node_main(self):
		global barrier
		print("node {} is up".format(self.nid))
		print("node {} init with {} stakes and connected to {}".format(self.nid, self.stake, [l.endpoint for l in self.conn]), file=self.f)
		tr = threading.Thread(target=self.recv)
		tr.start()
		ts = threading.Thread(target=self.send)
		ts.start()
		while True:
			vrf_output, j = self.sortition(tau_proposer)
			hp, idx = self.highest_priority(vrf_output, j)
			if (j>0):
				mesg = self.gen_prio_mesg(vrf_output, j, hp)
				self.gossip(mesg)
				# print ("{} is proposer for round {}".format(self.nid, self.rinfo.round_num))
			time.sleep(lambda_proposer)
			# update to maxprio will stop as lambda proposer has passed in sleep. 
			if (j>0 and hp <= self.rinfo.maxprio):
				# print ("highest priority in round {} is {} by {} accd to {}".format(self.rinfo.round_num, self.rinfo.maxprio, self.rinfo.mpuid, self.nid))
				mesg1 = self.gen_blk_mesg(vrf_output, j, hp)
				mesg2 = self.gen_blk_mesg(vrf_output, j, hp)
				byz_sem.acquire()
				if byz_mesg[2]<self.rinfo.round_num:
					byz_mesg[0] = mesg1
					byz_mesg[1] = mesg2
					byz_mesg[2] = self.rinfo.round_num
				byz_sem.release()
				self.gossip(mesg1)
				self.gossip(mesg2)
			tl = threading.Thread(target=self.lookout)
			tl.start()
			time.sleep(lambda_blk)
			tl.join(0.001)
			self.rinfo.step+=1
			hblock = self.reduction(self.rinfo.blkhash)
			hblock_ = self.binaryBA(self.rinfo.blkhash)
			r = self.countVotes(3+MAXSTEPS, threshold_final, tau_final, lambda_step)
			blk = None
			if (hblock_ == r):
				blk = Block(self.rinfo.prevhash, calc_SHA256(r), 1) # rnd number = sha of block hash
			elif hblock_ == bytes(32):
				blk = Block(self.rinfo.prevhash, bytes(32), 0)
			else:
				blk = Block(self.rinfo.prevhash, calc_SHA256(hblock_), 0)
			print("\npriority messages received during round {}".format(self.rinfo.round_num), file=self.f)
			for key, val in self.rinfo.prio_recv.items():
				print("priority = {}, vrf_output = {}, sub_user_idx = {} by {}".format(key, val[0].vrf_output[0:8], val[0].sub_userid, val[1]), file=self.f)
			print("\nBlock proposal messages received during round {}".format(self.rinfo.round_num), file=self.f)
			for key, val in self.rinfo.blk_recv.items():
				print("block hash = {}, priority = {}, prevhash = {} by {}".format(key[0:8], val[0].prio_pl.priority, val[0].prevhash[0:8], val[1]), file=self.f)
			print ("\n{} Consensus acheived on block hash {} in round {}".format("FINAL" if blk.typec==1 else ("TENTATIVE" if hblock_!=0 else "NO"), hblock_, self.rinfo.round_num), file=self.f, flush=True)
			self.rsem.acquire()
			self.blockchain.append(blk)
			if hblock_ == bytes(32):
				self.rinfo = RoundInfo(calc_SHA256(blk.header+blk.data), self.rinfo.round_num+1)
			else:
				self.rinfo = RoundInfo(hblock_, self.rinfo.round_num+1)
			self.mode = 0
			self.vhash = None
			self.rsem.release()
			barrier.sem_wait(self.nid)

def dead_thr_collector():
	# run on a seperate thread
	global temp_threads
	while not brexit:
		t = temp_threads.get()
		t.join(1)
		if(t.is_alive()):
			temp_threads.put(t)

def constr_network(rem):
	global node, N, gblprng
	# print(rem)
	fn = 1
	i = 0
	while i<N and fn<N:
		j = 0
		while (fn != N) and j<2:
			bd = max(0, gblprng.gauss(mu_blk, sigma_blk))
			nbd = max(0, gblprng.gauss(mu_nonblk, sigma_nonblk))
			rem[i] -= 1
			rem[fn] -= 1
			node[i].conn.append(Link(fn, bd, nbd))
			node[fn].conn.append(Link(i, bd, nbd))
			# print ("{} conn {}, rem = {}, {}".format(i, fn, rem[i], rem[fn]))
			j+=1
			fn+=1
		i+=1

	for j in range(0, N):
		t = 0
		while rem[j]!=0 and t<50:
			rn = gblprng.randint(min(j+1,N-1), N-1)
			t+=1
			# print("try conn {} with {}".format(j, rn))
			if(rem[rn]==0 or (rn in [l.endpoint for l in node[j].conn]) or rn==j):
				continue
			bd = max(0, gblprng.gauss(mu_blk, sigma_blk))
			nbd = max(0, gblprng.gauss(mu_nonblk, sigma_nonblk))
			rem[rn] -= 1
			rem[j] -= 1
			node[rn].conn.append(Link(j, bd, nbd))
			node[j].conn.append(Link(rn, bd, nbd))
			# print("conn {} with {}, rem = {}, {}".format(j, rn, rem[j], rem[rn]))
	# for j in range(0, N):
	# 	assert(rem[j]==0)

if __name__ == '__main__':
	fillchoose()
	rem = [0]*N
	sum = 0
	sn = None
	print ("initializing nodes")
	for i in range(0, N):
		nd = Node(i)
		node.append(nd)
		rem[i] = nd.m
		sum += nd.m
		if (nd.m in [5,6,7,8]):
			sn = i
	if (sum%2==1):
		node[sn].m-=1
		rem[sn]-=1
	print ("Constructing the Network")
	constr_network(rem)
	print ("Total stakes {}".format(sum_stakes))
	for i in range(0, N):
		t = threading.Thread(target=node[i].node_main)
		t.start()
	dth = threading.Thread(target=dead_thr_collector)
	dth.start()


# add barier at the end of the round to maintain sync
# do not forget to consider yourself in highest priority
# see that mesg sequence number is updated.
# INVARIANT step num is used in many places be sure its correctly updated and used
# be sure to count your own votes
# check if its from old round 
# consider your own blk proposer