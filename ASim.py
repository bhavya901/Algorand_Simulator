import queue
import random
import hashlib
from ecdsa import SigningKey
import threading
import time
from scipy.special import comb
from threading import Semaphore
import time

class Block:

	def __init__(self, prevhash, rnd_bytes, _data=bytes(0)):
		# prevhash, rnd_bytes and header are of type bytes
		self.header =  prevhash + rnd_bytes
		self.data = _data

# bytes(32) in rnd_bytes signifies empty block

genblock = Block(bytes(32), bytes(32), "We are building the best Algorand Discrete Event Simulator".encode("utf-8"))
N = 2000 # number of node
gblprng = random.Random()
node = []
mu_blk, sigma_blk, mu_nonblk, sigma_nonblk = 200, 400, 30, 64
tau_proposer, tau_step, tau_final = 20, 200, 200 # TODO
lambda_proposer, lambda_blk, lambda_step =  3, 30, 3
threshold_step, threshold_final = 0.67, 0.67 # TODO 
sum_stakes = 0
MAXSTEPS = 15
brexit = False
temp_threads = queue.Queue(0)

def calc_SHA256(s):
	# s = string
	sha_256 = hashlib.sha256()
	sha_256.update(s.encode('utf-8'))
	byts = sha_256.digest()
	return byts

def PRG(seed):
	# seed is of type bytes, return bytes
	local_prng = random.Random(seed)
	num = local_prng.getrandbits(256)
	return num.to_bytes(32, 'little')
	# return num

class Link:

	def __init__(a, bd, nbd):
		self.endpoint = a
		self.blk_delay = bd
		self.nonblk_delay = nbd

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

	def __init__(self, ptype):
		self.type = ptype
		self.byts = None


class PriorityPayload(Payload):

	def __init__(self, round_num, vrf_output, sub_userid, priority):
		self.round = round_num
		self.vrf_output = vrf_hash_output
		self.sub_userid = sub_userid
		self.priority = priority
		byts = self.round.to_bytes(4, 'little') + vrf_output + self.sub_userid.to_bytes(4, 'little') + priority
		Payload.__init__(self, 0, byts)

class BlkPayload(Payload):

	def __init__(self, prevhash, rnd_num, priority_payload):
		self.prevhash = prevhash
		self.random = rnd_num
		self.prio_pl = priority_payload
		byts = prevhash + self.round.to_bytes(4, 'little') + self.prio_pl.byts
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

	def __init__(self, prevhash, round_num, ):
		global MAXSTEPS
		self.prevhash = prevhash
		self.round_num = round_num
		self.step = 0 # current step
		self.maxprio = (1<<256)-1;
		self.mpuid = -1
		self.mesg_seq = 0
		self.ptime_st = time.time()
		self.inc_mesg = [queue.Queue(0) for i in range(0, 3+MAXSTEPS)] # sem not needed to access

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
		self.m = self.pnrg.randint(4,8)
		self.conn = []
		self.sk = SigningKey.generate()
		self.pk = self.sk.get_verifying_key()
		self.seen_mesg = {}
		# TODO require mutex for atomic updates
		# TODO INVARIANT MAINTAIN of round info
		self.rinfo = RoundInfo(calc_SHA256(genblock.header+genblock.data), 1)
		self.rsem = Semaphore(1)


	# returns vrf_output (bytes), #sub_user
	def sortition(self, tau):
		global sum_stakes
		self.rsem.acquire()
		seed = self.hashprev + self.rinfo.round_num.to_bytes(4, 'little') + self.rinfo.step.to_bytes(4, 'little')
		self.rsem.release()
		vrf_output = sign(PRG(seed))
		p, j, w = tau/sum_stakes, 0, self.stake
		roulette = vrf_output/(1<<48)
		ll, ul = 0, scipy.special.comb(w, j, True)*pow(1-p, w-j)*1 # TODO if required approx. maht.pow, falsein comb
		while not(roulette>=ll and roulette<ul):
			j+=1
			ll = ul
			ul += scipy.special.comb(w,j, True)*pow(1-p, w-j)*pow(p, j)
			if(j==w):
				break
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
		self.rsem.acquire()
		if(hp < self.rinfo.maxprio):
			self.rinfo.maxprio = hp
			self.rinfo.mpuid = (self.nid, idx)
		self.rsem.release()
		return (hp, idx)

	def recv(self):
		# run on a seperate thread
		global node,  brexit
		while !brexit:
			mesg, sender = self.recvq.get()  # blk until 
			# TODO logic for seen mesg, do not resend your own mesg
			# TODO verifying if sortition is done correctly
			if not node[mesg.OP].pk.verify(mesg.sign, mesg.payload.byts):
				continue
			# TODO triggers, state change
			prop = self.process(mesg, sender)
			# spreading gossip
			if (prop):
				for l in self.conn:
					if l.endpoint != sender:
						self.sendq.put( (mesg, l) )

	def send(self):
		# run on seperate thread
		global temp_threads
		while !brexit:
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

	def process(self, mesg, sender):
		# returns a bool which tells whether to prop further
		if(mesg.payload.type == 0):
			# priority message
			self.rsem.acquire()
			if(time.time() > self.rinfo.ptime_st + 3):
				self.rsem.release()
				return 1
			if (mesg.payload.priority < self.rinfo.maxprio):
				self.rinfo.maxprio = mesg.payload.priority
				self.rinfo.mpuid = (mesg.OP, mesg.payload.sub_userid)
				self.rsem.release()
				return 1
			self.rsem.release()
			return 0 # discards message with now priority than max prio seen 
		# TODO

	def committeeVote(self, tau, blkhash):
		vrf_output, j = self.sortition(tau)
		if(j>0):
			mesg = self.gen_vote_mesg(j, vrf_output, blkhash)
			self.gossip(mesg)
			# TODO send yourself the vote

	def countVotes(self, step, thr, tau, wait_time):
		# rsem not used see if its correct
		st = time.time()
		cnts = {}
		voters = set()
		while True:
			try:
				mesg = self.rinfo.inc_mesg[step].get(block=True, timeout=.05)
			except queue.Empty:
				if(time.time() > st+wait_time):
					return -1
				continue
			if (mesg.payload.prevhash != self.rinfo.prevhash) or (mesg.OP in voters):
				continue
			voters.add(mesg.OP)
			cnts[mesg.payload.blkhash] += mesg.payload.num_votes
			if( cnts[mesg.payload.blkhash] > thr*tau):
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
		if h2hash==-1:
			return bytes(32)
		return h2hash

	# def binaryBA(self, blkhash):
	# 	global MAXSTEPS
	# 	assert(self.rinfo.step == 3)
	# 	r = blkhash
	# 	empty_hash = bytes(32)
	# 	while(self.rinfo.step < MAXSTEPS):
	# 		self.committeeVote(tau_step, r)
	# 		r = self.countVotes(self.rinfo.step, threshold_step, tau_step, lambda_step)
	# 		if r== -1:
	# 			r = blkhash
	# 		elif r != empty_hash:



	def gen_prio_mesg(self, vrf_output, j, priority):
		self.rsem.acquire()
		payload = PriorityPayload(self.rinfo.round_num, vrf_output, j, priority)
		mesg = Message(payload, self.nid, self.rinfo.mesg_seq, self.sign(payload.byts), 0)
		self.rinfo.mesg_seq+=1
		self.rsem.release()
		return mesg

	def gen_blk_mesg(self, vrf_output, j, priority)
		self.rsem.acquire()
		prio_pl = PriorityPayload(self.rinfo.round_num, vrf_output, j, priority) 
		payload = BlkPayload(self.rinfo.prevhash, self.prng.getrandbits(256), prio_pl)
		mesg = Message(payload, self.nid, self.rinfo.mesg_seq, self.sign(payload.byts), 1)
		self.rinfo.mesg_seq+=1
		self.rsem.release()
		return mesg

	def gen_vote_mesg(self, num_votes, vrf_output, blkhash):
		self.rsem.acquire()
		payload = VotePayload(self.rinfo.prevhash, self.rinfo.round_num, self.rinfo.step, num_votes, vrf_output, blkhash)
		mesg = Message(payload, self.nid, self.rinfo.mesg_seq, self.sign(payload.byts), 0)
		self.rinfo.mesg_seq+=1
		self.rsem.release()
		return mesg

def dead_thr_collector():
	# run on a seperate thread
	global temp_threads
	while !brexit:
		t = temp_threads.get()
		t.join(1)
		if(t.is_alive()):
			temp_threads.put(t)

def constr_network(rem):
	global node, N, gblprng
	fn = 1
	i = 0
	while i<N and fn<N:
		j = 0
		while (fn != N) and j<2:
			bd = max(0, gblprng.guass(mu_blk, sigma_blk))
			ndb = max(0, gblprng.guass(mu_nonblk, sigma_nonblk))
			rem[i] -= 1
			rem[fn] -= 1
			node[i].conn.append(Link(fn, bd, nbd))
			node[fn].conn.append(Link(i, bd, nbd))
			j+=1
			fn+=1
		i+=1

	for j in range(0, N):
		while rem[j]!=0:
			rn = gblprng.randint(0, N-1)
			if(rn==j or rem[rn]==0):
				continue
			bd = max(0, gblprng.guass(mu_blk, sigma_blk))
			ndb = max(0, gblprng.guass(mu_nonblk, sigma_nonblk))
			rem[rn] -= 1
			rem[j] -= 1
			node[rn].conn.append(Link(j, bd, nbd))
			node[j].conn.append(Link(rn, bd, nbd))

	for j in range(0, N):
		assert(rem[j]==0)

def main():
	global N, node
	rem = [0]*N
	sum = 0
	sn = None
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
	constr_network(rem)




# add barier at the end of the round to maintain sync
# do not forget to consider yourself in highest priority
# see that mesg sequence number is updated. 
# INVARIANT step num is used in many places be sure its correctly updated and used
# be sure to count your own votes