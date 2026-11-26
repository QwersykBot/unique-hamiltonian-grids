#!/usr/bin/env python3
"""Check m=10 all-length sign certificate, using integers and the Python stdlib.

No symbolic-algebra dependency, numerical eigenvalue, or extrapolation from a
finite prefix is used. The proof's induction is explained in README-sign.txt.
"""
import argparse,hashlib,importlib.util,json,time
from pathlib import Path

if not __debug__:
    raise SystemExit('Run without -O, -OO, or PYTHONOPTIMIZE.')

def mv(matrix, vector):
    return [sum(a*b for a,b in zip(row,vector)) for row in matrix]

def dot(x,y):return sum(a*b for a,b in zip(x,y))

def trim(p):
    p=list(p)
    while len(p)>1 and p[-1]==0:p.pop()
    return p

def multiply(p,q):
    out=[0]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        for j,b in enumerate(q):out[i+j]+=a*b
    return trim(out)

def rebuild(repo,width):
    spec=importlib.util.spec_from_file_location('checked_cylinder_model',repo/'checks/check_cylinder_model.py')
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    model=module.model(width);audit=module.audit_model(model)
    Q=audit['quotient_row_weights'];J=audit['quotient_J_zero_based']
    initial=audit['quotient_initial_weights'];keys=audit['quotient_representatives']
    words={''.join(map(str,word)):state for state,word in model['words'].items()}
    chosen=[i for i,j in enumerate(J) if i<j]
    A=[[Q[i][j]-Q[i][J[j]] for j in chosen] for i in chosen]
    u=[initial[i]-initial[J[i]] for i in chosen]
    v=[int(words[keys[i]] in model['Lc'])-int(words[keys[i]] in model['Lnc']) for i in chosen]
    # Fixed orbits have no odd component. The actual J endpoint-exchange and
    # matrix-commutation assertions are checked by audit_model above.
    assert all(int(words[keys[i]] in model['Lc'])==int(words[keys[i]] in model['Lnc'])
               for i,j in enumerate(J) if i==j)
    return A,u,v,[keys[i] for i in chosen],audit

def verify(cert_path,repo):
    start=time.monotonic();c=json.loads(cert_path.read_text());source=repo/'checks/check_cylinder_model.py'
    assert hashlib.sha256(source.read_bytes()).hexdigest()==c['source_checker_sha256']
    A,u,v,representatives,audit=rebuild(repo,c['width'])
    assert (A,u,v,representatives)==(c['signed_transfer_A'],c['initial_row_u'],c['terminal_column_v'],c['representatives'])
    d=len(A);assert d==c['odd_quotient_dimension']
    B=[[-z for z in row] for row in A]
    q=c['annihilator_of_minus_A_coefficients_desc'];assert len(q)==d+1 and q[0]==1
    # Exact vector identity q(B)v=0 is sufficient for the scalar recurrence:
    # multiplying by u B^n gives q(E)a_n=0 for every n>=0.
    residue=[q[0]*z for z in v]
    for coefficient in q[1:]:
        residue=[x+coefficient*y for x,y in zip(mv(B,residue),v)]
    assert residue==[0]*d,'annihilator fails'
    seq=[];current=v[:]
    for k in range(d+1):
        seq.append(dot(u,current));current=mv(B,current)
    # Construct the exact numerator for full denominator sum q_j z^j.
    full_numerator=[sum(q[j]*seq[i-j] for j in range(i+1)) for i in range(d)]
    p=c['positive_sequence_reduced_numerator_asc'];den=c['positive_sequence_reduced_denominator_asc']
    assert den[0]==1 and len(p)<len(den)
    assert multiply(full_numerator,den)==multiply(p,q),'rational-function identity fails'
    # Synthetic division of x^s den(1/x) by (x-r).
    r=c['growth_r'];assert isinstance(r,int) and r>=1
    horner=[den[0]]
    for coefficient in den[1:]:horner.append(coefficient+r*horner[-1])
    assert horner[0]==1 and all(x<=0 for x in horner[1:-1]) and horner[-1]<0
    s=len(den)-1;assert seq[0]>0
    differences=[seq[k+1]-r*seq[k] for k in range(s-1)]
    assert all(x>0 for x in differences),'initial positive cone fails'
    # Independent unquotiented full-state count replay at enough initial widths.
    # These are validation of the endpoint conventions, not the induction proof.
    cpp=cert_path.parent/'cpp-10.json'
    cpp_terms=0
    if cpp.exists():
        record=json.loads(cpp.read_text());assert record['m']==c['width']
        assert all(seq[k]==((-1)**k)*record['counts'][k][3] for k in range(d+1))
        cpp_terms=d+1
    return {
      'status':'PASS','width':c['width'],'model_states':audit['actual_states'],
      'dihedral_quotient_states':audit['quotient_states'],'odd_block_dimension':d,
      'annihilator_degree':d,'reduced_recurrence_degree':s,'r':r,
      'cone_remainder':horner[-1],'minimum_initial_difference':min(differences),
      'q_B_v_zero':True,'exact_rational_identity':True,'positive_induction_conditions':True,
      'independent_cpp_terms_compared':cpp_terms,
      'source_checker_sha256':c['source_checker_sha256'],
      'certificate_sha256':hashlib.sha256(cert_path.read_bytes()).hexdigest(),
      'elapsed_seconds':time.monotonic()-start,
      'scope':'All lengths for this reconstructed m=10 transfer model; no all-circumference conclusion.'
    }

if __name__=='__main__':
    parser=argparse.ArgumentParser();base=Path(__file__).resolve().parent
    parser.add_argument('--certificate',type=Path,default=base/'m10-all-length-sign-certificate.json')
    parser.add_argument('--repository',type=Path,default=base.parent/'unique-hamiltonian-grids')
    args=parser.parse_args();print(json.dumps(verify(args.certificate,args.repository),indent=2))
